// Часть I, шаг 2, страницы (2026-11-13, слово автора «Делай»): вариант А развилки (L3_independence — настоящая
// независимость под тем же именем), 19 правок главы I.3 и правка 1а главы I.5 внесены.
// Запуск: node patch-p01-step-02-pages.cjs   (затем relocate + merge по part01-ch03 и part01-ch05)
// Скрипт повторяем: приведённая запись пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть I, шаг 2, слово автора)';
const F = 'src/foundation/';
const CD = F + 'DistinctionCoDefinition.v';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  return {
    // th: undefined — любая запись; null — запись без теоремы; строка — запись с этой теоремой
    fix(prefix, th, fields, keepVerdict) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) &&
        (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
      if (hit.length === 0) return;
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix.slice(0, 50) + '» / ' + th + ', найдено ' + hit.length);
      Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
    },
    add(rec) {
      if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); },
  };
}
const L3NEW = 'L3_independence (LawsFromDistinction.v, с 13.11): exists p n : Prop, (p = p /\\ n = n) /\\ ~ (p /\\ n) /\\ (p -> ~ n) /\\ (forall l : Level, ~ (l << l)) /\\ ~ (p \\/ n); свидетель False, False. Closed under the global context. Прежняя формулировка — (forall D, positive D \\/ negative D) -> forall P, P \\/ ~ P — отбрасывала посылку и брала заключение из classic; снята по слову автора (вариант А).';
const a = open('part01-ch03.json');

// место 2
a.fix('Закон Тождества $L1$ опирается на поля `positive` и `negative`', 'L1_through_distinction', {
  claim: 'Закон Тождества $L1$ относится к полям `positive` и `negative` (тождественность сторон).',
  note: DONE + ': было «опирается на поля». Теоремы L1 — x = x, рефлексивность равенства; свойств записи доказательство не использует — страница теперь говорит это (стр. 212–214, 1251).' });
a.fix('Закон Достаточного Основания $L4$ опирается на саму структуру записи как целого', 'Law_of_SufficientReason', {
  claim: 'Закон Достаточного Основания $L4$ опирается на саму структуру записи как целого — через требование обоснований для всех полей; теоремой в файле представлена одна его сторона — самообоснование, выводимое из поля `exclusive`.',
  note: DONE + ': добавлено, что теоремой представлено самообоснование из поля exclusive (Law_of_SufficientReason, L4_contra — из L4_self_grounding, Distinction.v). Closed under the global context.' });
a.fix('Это соответствие — не риторическое наблюдение. В настоящей главе каждое из перечисленных утверждений', null, {
  claim: 'Это соответствие — не риторическое наблюдение. В настоящей главе для каждого из перечисленных законов будет предъявлена теорема Rocq о сторонах записи, и при каждом законе будет сказано, чем она обеспечена: полем записи, шагом вывода из поля, рефлексивностью равенства или аксиомой.',
  note: DONE + ': было «каждое из перечисленных утверждений будет формально доказано». Страница называет, чем обеспечена каждая теорема.' });
a.fix('Тривиальность доказательств — признак того, что *запись* `Distinction` уже несёт', 'L1_through_distinction', {
  claim: 'Тривиальность доказательств — признак того, что для $L1$ достаточно самой типизации: равенство в CIC рефлексивно для любого терма, и сторонам записи `Distinction` достаточно быть термами типа `Prop`.',
  note: DONE + ': было «запись Distinction уже несёт в себе всю необходимую информацию для L1».' });
a.fix('$L1$ — на поля `positive` и `negative` (через рефлексивность их типов `Prop`);', 'L1_through_distinction', {
  claim: '$L1$ — на поля `positive` и `negative` (через рефлексивность равенства на типе `Prop`; иных свойств записи доказательство не требует);',
  note: DONE + ': было «через рефлексивность их типов Prop».' });
// место 1
a.fix('Тем не менее, в рамках *формальной системы* Rocq законы логики могут быть *выведены как теоремы*', null, {
  theorem: 'sides_codetermined', file: CD,
  note: DONE + ': формула автора сохранена; следом добавлена роспись — L2 и L3 для сторон даны полями, L4 выведен из exclusive, L1 — рефлексивность равенства, L3 в общей форме — аксиома classic, L5 — о типе Level; выводом из обоих полей названа со-определённость сторон (sides_codetermined, Closed under the global context).' });
// место 3
a.fix('$L3$ имеет три формы — общую через аксиому `classic`', 'L3_independence', {
  claim: '$L3$ имеет три формы — общую через аксиому `classic`, структурную через поле `exhaustive` и теорему независимости `L3_independence`.',
  note: DONE + ': было «теорему равносильности». ' + L3NEW });
a.fix('Она утверждает: исключённое третье для всякого акта различения влечёт', 'L3_independence', {
  claim: 'Она утверждает: есть пара сторон, для которой выполнены $L1$, $L2$, $L4$ и $L5$, а $L3$ не выполнен, — обе стороны ложны, и между ними остаётся «третий путь». Доказана она без аксиом.',
  page_price: 'без аксиом', note: DONE + '. ' + L3NEW });
a.fix('Вместе с `L3_from_distinction`, дающей обратное направление, это показывает', 'L3_independence', {
  theorem: 'every_prop_distinguishes_iff_EM', file: CD, page_price: 'без аксиом',
  claim: 'Совпадение это доказано отдельно, в обе стороны и тоже без аксиом: «всякая пропозиция есть положительная сторона некоторого различения» равносильно исключённому третьему для всякой пропозиции (`every_prop_distinguishes_iff_EM`, файл `DistinctionCoDefinition.v`).',
  note: DONE + ': было «L3-через-различение и classic равносильны по силе… в обе стороны» — со ссылкой на теорему, посылка которой не работала. every_prop_distinguishes_iff_EM : (forall P, exists D, positive D = P) <-> (forall P, P \\/ ~ P). Closed under the global context.' });
a.fix('Теорема фиксирует внутренне доступную часть: точное совпадение', 'L3_independence', {
  claim: 'Теорема фиксирует внутренне доступную часть: независимость $L3$ от остальных законов на паре сторон.',
  note: DONE + ': было «точное совпадение L3-через-различение и classic». ' + L3NEW });
// место 4
const P4 = 'Глава 3 даёт формальный коррелят: без поля `exhaustive` теорема `L3_from_distinction` не была бы доказуемой — пара сторон, обе из которых ложны, удовлетворяет исключительности, и ни одна из сторон не имеет места (`third_way_without_exhaustive`, `exhaustive_not_from_exclusive`).';
a.fix('Глава 3 даёт формальный коррелят: без поля `exhaustive` теорема `L3_from_distinction` не была бы доказуемой; пришлось бы', 'L3_from_distinction', {
  claim: P4, note: DONE + ': было «пришлось бы для каждого конкретного D отдельно применять classic» — classic даёт positive D \\/ ~ positive D и стороны не связывает; страница теперь говорит это и называет леммы о независимости полей.' });
a.add({ theorem: 'third_way_without_exhaustive', file: CD, claim: P4,
  note: 'third_way_without_exhaustive : exists p n, ~ (p /\\ n) /\\ ~ p /\\ ~ n. Closed under the global context.' });
a.add({ theorem: 'exhaustive_not_from_exclusive', file: CD, claim: P4,
  note: 'exhaustive_not_from_exclusive : ~ (forall p n, ~ (p /\\ n) -> p \\/ n). Closed under the global context.' });
// место 5
a.fix('Это — формальный след тезиса о детерминированности существования, и его *не следует* смешивать с Аксиомой Выбора', 'L4_witness', {
  note: DONE + ': фраза автора сохранена; следом добавлено, что по силе аксиома от выбора не отделена (записана без условия единственности свидетеля) и что граница проходит по единственности свидетеля — согласовано с главой 10.4.' });
a.add({ theorem: 'l4_statement_gives_functional_choice', file: 'src/settheory/ChoicePriceMap.v', page_price: '',
  claim: 'По силе они при этом не разделены: аксиома записана без условия единственности свидетеля и, применённая к каждому члену семейства, даёт выбирающую функцию (`l4_statement_gives_functional_choice`); граница между L4 и выбором проходит по тому, единствен ли свидетель (Глава 10.4).',
  note: 'l4_statement_gives_functional_choice : L4_statement -> forall I X R, (forall i, exists x, R i x) -> exists f, forall i, R i (f i). Closed under the global context (L4 — посылкой).' });
// место 6
const L5N = 'L5_no_infinite_descent : forall l1 l2 : Level, l1 << l2 -> (level_depth l1 < level_depth l2)%nat (LawsFromDistinction.v; формулировка с июня 2026 г.). Closed under the global context.';
a.fix('У каждого уровня есть конечная глубина:', 'L5_no_infinite_descent', {
  claim: 'Глубина строго убывает вдоль порядка:', note: DONE + ': блок кода и разбор приведены к нынешней формулировке. ' + L5N });
a.fix('Формально теорема доказывает более слабое утверждение: каждому уровню сопоставляется конечная натуральная глубина', 'L5_no_infinite_descent', {
  claim: 'Формально теорема доказывает утверждение о мере: каждый шаг вниз по порядку уменьшает натуральное число — глубину уровня.',
  note: DONE + ': было — описание прежней формулировки («конечная натуральная глубина»). ' + L5N });
a.fix('тогда как сама теорема `L5_no_infinite_descent` фиксирует лишь конечность глубины.', 'L5_no_infinite_descent', {
  theorem: 'no_infinite_level_regress', file: F + 'MetaPairStrength.v', page_price: 'без аксиом',
  claim: 'Но это утверждение из неё следует — натуральное число не может убывать бесконечно — и в репозитории доказано отдельно, без аксиом (`no_infinite_level_regress`, файл `MetaPairStrength.v`).',
  note: DONE + ': было «сама теорема фиксирует лишь конечность глубины». no_infinite_level_regress : forall f : nat -> Level, ~ (forall n, level_lt (f (S n)) (f n)). Closed under the global context.' });
// место 7
a.fix('Эти объединяющие теоремы — не сумма уже сказанного, а самостоятельные формальные утверждения', 'five_laws_from_distinction', {
  claim: 'Эти объединяющие теоремы собирают уже доказанное в одно утверждение и тем показывают, что законы работают *совместно* в одной и той же записи `Distinction`, в одной и той же иерархии `Level`, согласованно друг с другом.',
  note: DONE + ': было «не сумма уже сказанного, а самостоятельные формальные утверждения». Три из четырёх объединяющих теорем — конъюнкции доказанного; утверждение, которому два поля нужны вместе, названо следом (sides_codetermined).' });
a.add({ theorem: 'sides_codetermined', file: CD,
  claim: 'Утверждение, которому два правила записи нужны именно вместе, — со-определённость сторон (`sides_codetermined`): оно не следует ни из одного поля в отдельности.',
  note: 'sides_codetermined : forall D, (negative D <-> ~ positive D) /\\ (positive D <-> ~ negative D). Closed under the global context. Ни из одного поля в отдельности не следует: codefinition_needs_exclusive, codefinition_needs_exhaustive.' });
// место 8
a.fix('Объединяющая теорема даёт каждый из пяти законов в его *полной* форме.', 'five_laws_from_distinction', {
  claim: 'Объединяющая теорема даёт каждый из пяти законов в его *структурной* форме, не урезая её.',
  note: DONE + ': было «в его полной форме». В конъюнкции — по одной структурной форме каждого закона.' });
a.fix('Таким образом, теорема не урезает ни одного из законов ради краткости', 'five_laws_from_distinction', {
  page_price: 'без аксиом',
  claim: 'Общая форма $L3$ для произвольной пропозиции (на аксиоме `classic`), контрапозиция и двойное отрицание из блока $L4$, транзитивность и убывание глубины из блока $L5$ в конъюнкцию не входят — поэтому теорема доказана без аксиом.',
  note: DONE + ': было «каждый из пяти конъюнктов есть закон в той же силе, в какой он разобран отдельно». five_laws_from_distinction — Closed under the global context.' });
// место 10
a.fix('Это — структурное условие *полноты разделения*, в котором появляется зависимость от аксиомы `classic`', 'L3_L4_combined', {
  page_price: 'без аксиом',
  claim: 'Это — структурное условие *полноты разделения*; сама парная теорема доказана без аксиом — исчерпанность берётся из поля `exhaustive`, — а зависимость от аксиомы `classic` появляется там, где различение строится для произвольной пропозиции (`distinction_of`).',
  note: DONE + ': было «появляется зависимость от аксиомы classic (через exhaustive)». L3_L4_combined — Closed under the global context.' });
a.fix('Парные объединения, таким образом, не дублируют общую пятёрку, а *структурируют* её на два уровня', 'L3_L4_combined', {
  page_price: 'без аксиом',
  claim: 'Парные объединения, таким образом, не дублируют общую пятёрку, а *структурируют* её на два блока: определённость и несовместность ($L1, L2$) и полноту с обоснованностью ($L3, L4$). Обе парные теоремы доказаны без аксиом; классической аксиомы требуют общие формы для произвольной пропозиции — `Law_of_ExcludedMiddle` и `L4_double_negation`.',
  note: DONE + ': было «условия, требующие классической аксиомы (L3, L4 в полной форме)». L1_L2_combined, L3_L4_combined — Closed; Law_of_ExcludedMiddle, L4_double_negation — Distinction.classic.' });
// место 9
a.fix('Запись `Distinction` с четырьмя полями и тип `Level` с оператором порядка — это *одна* формальная структура', null, {
  claim: 'Запись `Distinction` с четырьмя полями и тип `Level` с оператором порядка — две согласованные части *одной* формализации, в которой все пять законов получают свои формальные представления: законы одного акта читаются из записи, закон порядка — из типа уровней (запись и тип объявлены отдельно; теоремы, связывающей различение с его уровнем, в файле нет).',
  note: DONE + ': было «это одна формальная структура». Distinction и Level — два независимых объявления; фраза автора о чтении из одной структуры сохранена. Связь различения с уровнем — горизонт (новая конструкция).' });
a.fix('Совокупность теорем `LawsFromDistinction.v` показывает иное — что простейший формализуемый объект', null, {
  claim: 'Совокупность теорем `LawsFromDistinction.v` показывает иное — что простейший формализуемый объект (запись `Distinction`) уже несёт в себе законы одного акта — $L1$–$L4$ — как свои *структурные свойства*, доступные для машинной проверки, а закон порядка $L5$ столь же прямо читается из типа `Level`.',
  note: DONE + ': было «уже несёт в себе все пять законов». Теоремы L5 запись не упоминают — они о типе Level.' });
// сверх таблицы: laws_consistent
a.add({ theorem: 'laws_consistent', file: F + 'LawsFromDistinction.v', page_price: 'без аксиом',
  claim: '`laws_consistent` показывает, что построение возможно, — и показывает без аксиом: экземпляр предъявлен прямо, со сторонами `True` и `False`.',
  note: DONE + ': было «универсальная конструкция distinction_of (P)… даёт нужный экземпляр». С шага 2 свидетель — mkDistinction True False …; Closed under the global context.' });
a.save();

// ------------------------------------------------------------------ глава I.5, правка 1а (слово автора 13.11)
const b = open('part01-ch05.json');
const C1A = 'В формализации это три утверждения без аксиом: различения с данными сторонами нет в точности тогда, когда стороны не со-определены, и тогда нет и потенциала (`absent_iff_not_codefined`, `absent_iff_no_potential`); потенциал от различения отделяет одно назначение стороны (`actual_iff_potential_and_assignment`); потенциал, которому отказано в завершении, противоречив — четвёртого нет (`no_partial_distinction`).';
const W = 'Внесено 13.11 по слову автора («это не ограничение ТоС, а самой логики — различие либо есть, либо нет; и так же возможен потенциал для различия; других вариантов по построению нет»). ';
b.add({ theorem: 'absent_iff_not_codefined', file: CD, page_price: 'без аксиом', claim: C1A,
  note: W + 'absent_iff_not_codefined : ~ actual_on p n <-> ~ (n <-> ~ p). Closed under the global context.' });
b.add({ theorem: 'absent_iff_no_potential', file: CD, page_price: 'без аксиом', claim: C1A,
  note: W + 'absent_iff_no_potential : ~ actual_on p n <-> ~ potential_on p n. Closed under the global context.' });
b.add({ theorem: 'actual_iff_potential_and_assignment', file: CD, page_price: 'без аксиом', claim: C1A,
  note: W + 'actual_iff_potential_and_assignment : actual_on p n <-> (potential_on p n /\\ (p \\/ n)). Closed under the global context.' });
b.add({ theorem: 'no_partial_distinction', file: CD, page_price: 'без аксиом', claim: C1A,
  note: W + 'no_partial_distinction : ~ (potential_on p n /\\ ~ actual_on p n). Closed under the global context.' });
b.save();
