// Часть X, шаг 1, страницы (2026-11-13, слово автора «Да»): восемнадцать мест главы X.3 внесены.
// Записи ведомости приводятся к новым словам страницы; добавляются записи о новых теоремах.
// Запуск: node patch-p10-step-01-pages.cjs   (затем tom-links.cjs relocate + merge ведомости/part10-ch03.json)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть X, шаг 1, слово автора)';
const SB = 'src/SchroederBernstein_ERR.v';
const CW = 'src/settheory/CardinalityWithoutChoice.v';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part10-ch03.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
function set(prefix, fields) {
  const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  Object.assign(hit[0], { verdict: 'ok' }, fields); n++;
}
function add(rec) {
  if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
  j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
}
const DEF = 'Schroeder_Bernstein_definite : (forall P, P \\/ ~ P) -> (forall T P, (exists! x, P x) -> {x | P x}) -> forall A B f g, инъективность f и g -> exists h, инъективна и сюръективна. Closed under the global context. Прежняя Schroeder_Bernstein — её частный случай при classic и L4_definite (classic + L4_witness).';

set('Глава держится на двух столпах, оба — *без аксиомы выбора*:', { theorem: 'cardinal_antisym_definite', file: CW, page_price: 'без выбора',
  note: DONE + ': слова страницы прежние; теперь они опираются на теорему. cardinal_antisym_definite : ExcludedMiddle -> UniqueWitness -> forall A B, injects A B -> injects B A -> bijects A B — Closed under the global context: антисимметрия выводится из исключённого третьего и извлечения единственного свидетеля, выбор из многих свидетелей в посылки не входит.' });
set('Это делает предпорядок вложений *антисимметричным* с точностью до биекции — и доказывается без выбора, ценою', { theorem: 'Schroeder_Bernstein_definite', file: SB, page_price: 'без выбора; в формализации L3 и L4',
  claim: 'Это делает предпорядок вложений *антисимметричным* с точностью до биекции — и доказывается без выбора — из исключённого третьего и извлечения *единственного* свидетеля, на конечной глубине цепи; в формализации цена теоремы — L3 и L4 (не 0 аксиом).',
  note: DONE + ': было «без выбора, ценою L3 и L4». ' + DEF });
set('*обратный* мост — от сюръекции $A\\twoheadrightarrow B$ к вложению $B\\hookrightarrow A$ — это в точности', { theorem: 'surjects_injects_back', file: CW,
  claim: '*обратный* мост — от сюръекции $A\\twoheadrightarrow B$ к вложению $B\\hookrightarrow A$ — требует взять по прообразу в каждом слое сюръекции, а прообраз в слое не единствен. Это и есть выбор. В теории мощностей он живёт именно здесь: антисимметрии хватает *единственного* свидетеля, мосту нужен свидетель *произвольный*.',
  note: DONE + ': было «это в точности аксиома выбора. В ToS он не доказывается» — неверно: surjects_injects_back : surjects A B -> injects B A выводится из одного L4_witness. Антисимметрия — cardinal_antisym_definite, Closed under the global context.' });
set('Антисимметрия (Шрёдер–Бернштейн) и отсутствие максимума (Кантор) держатся без выбора; выбор локализуется', { theorem: 'cardinal_antisym_definite', file: CW, page_price: 'без выбора',
  note: DONE + ': слова страницы прежние; после шага 1 они опираются на теоремы: cardinal_antisym_definite (посылки — исключённое третье и единственный свидетель, Closed), no_maximal_cardinality (Closed), surjects_injects_back (L4_witness).' });
set('ToS заменяет завершённую бесконечную цепь *конечной глубиной* — натуральным числом: каждая точка либо', { theorem: 'chain_trichotomy', file: SB,
  claim: 'Цепь точки, прослеженная назад, либо за конечное число шагов обрывается в $B$ (на точке без прообраза), либо обрывается в $A$, либо не обрывается ни на какой глубине (`chain_trichotomy`). Биекция $h$ собирается по первому признаку:',
  note: DONE + ': было «каждая точка либо укоренена на конечной глубине, либо принадлежит двусторонне-бесконечной цепи». chain_trichotomy : (forall P, P \\/ ~ P) -> forall A B f g a, B_rooted f g a \\/ A_stops f g a \\/ never_stops f g a — Closed under the global context (исключённое третье — посылкой). B_rooted_iff_B_stops: признак файла есть «цепь обрывается в B».' });
set('Поэтому фундаментальная теорема о мощностях держится без выбора.', { theorem: 'Schroeder_Bernstein_definite', file: SB, page_price: 'без выбора',
  note: DONE + ': слова страницы прежние; теперь они опираются на теорему. ' + DEF });
set('Завершённая цепь заменена конечной глубиной (P4); цена — L3${}+{}$L4, не выбор.*', { theorem: 'Schroeder_Bernstein_definite', file: SB, page_price: 'L3 и единственный свидетель',
  claim: 'Завершённая цепь заменена конечной глубиной (P4); цена — L3 и извлечение единственного свидетеля, не выбор.*',
  note: DONE + ': было «цена — L3 + L4, не выбор». ' + DEF });
set('Именно этот обратный мост — *выбрать по одному прообразу для каждого $b\\in B$* — и есть аксиома выбора', { theorem: 'split_iff_choice', file: CW,
  claim: 'Именно этот обратный мост — *выбрать по одному прообразу для каждого $b\\in B$* — и есть выбор по слоям сюръекции: утверждение «у каждой сюръекции есть правая обратная» равносильно выбору функции по семейству (`split_iff_choice`).',
  note: DONE + ': было «и есть аксиома выбора… В ToS он не доказывается». split_iff_choice : surjections_split <-> functional_choice — Closed under the global context.' });
set('С одним лишь `L4_witness` можно обратить *биекцию* (прообразы единственны), но не произвольную сюръекцию', { theorem: 'surjects_injects_back', file: CW, page_price: 'один L4_witness',
  claim: 'Аксиома `L4_witness` в объявленном виде единственности не требует; применённая к каждому слою, она даёт правую обратную, и мост в формализации выводится (`surjects_injects_back`, цена — один `L4_witness`).',
  note: DONE + ': было «с одним лишь L4_witness можно обратить биекцию, но не произвольную сюръекцию» — неверно. surjects_injects_back : forall A B, surjects A B -> injects B A; Print Assumptions — ToS_Axioms.L4_witness.' });
set('Содержательные результаты главы — предпорядок, антисимметрия, отсутствие максимума — выбора не требуют;', { theorem: 'surjects_injects_back', file: CW,
  claim: 'Содержательные результаты главы — предпорядок, антисимметрия, отсутствие максимума — выбора не требуют; выбор локализован ровно в одном переходе, и цена этого перехода — `L4_witness` в полную силу.',
  note: DONE + ': было «в одном непроведённом переходе». Переход проведён: surjects_injects_back (L4_witness); антисимметрия — cardinal_antisym_definite (Closed).' });
set('*Сюръекция-в-инъекцию — это ровно место, где требуется выбор, и ToS его не проводит.', { theorem: 'surjects_injects_back', file: CW,
  claim: '*Сюръекция-в-инъекцию — это ровно место, где требуется выбор; в формализации его оплачивает `L4_witness`, взятый в полную силу. Антисимметрия живёт на инъекциях (L4 обращает единственное), а не на слоях сюръекции (где L4 выбирает из многих).*',
  note: DONE + ': было «ToS его не проводит». surjects_injects_back — L4_witness; bijects_sym_definite и cardinal_antisym_definite — Closed under the global context.' });
set('**Честные границы.** Обратный мост сюръекция${}\\to{}$инъекция — сам выбор, не проведён.', { theorem: 'surjects_injects_back', file: CW,
  claim: '**Честные границы.** Обратный мост сюръекция${}\\to{}$инъекция — выбор по слоям; в формализации он выводится ценой `L4_witness`, взятого в полную силу, и антисимметрии эта сила не нужна.',
  note: DONE + ': было «сам выбор, не проведён». surjects_injects_back — L4_witness; cardinal_antisym_definite — Closed under the global context.' });
set('*Сравнение мощностей — предпорядок ролей; антисимметрия (Шрёдер–Бернштейн) и отсутствие максимума (Кантор)', { theorem: 'cardinal_antisym_definite', file: CW,
  claim: '*Сравнение мощностей — предпорядок ролей; антисимметрия (Шрёдер–Бернштейн) и отсутствие максимума (Кантор) держатся без выбора (исключённое третье с единственным свидетелем и 0 аксиом соответственно); выбор локализован в переходе от сюръекции к инъекции, где L4 берётся в полную силу, и в линейности шкалы.*',
  note: DONE + ': было «(L3 + L4 и 0 аксиом соответственно); выбор локализован в единственном непроведённом переходе». cardinal_antisym_definite, no_maximal_cardinality — Closed; surjects_injects_back — L4_witness.' });
set('Аксиома выбора понадобилась бы лишь для обратного моста сюръекция${}\\to{}$инъекция и для линейности шкалы', { theorem: 'surjects_injects_back', file: CW,
  claim: 'Выбор понадобился лишь для обратного моста сюръекция${}\\to{}$инъекция — там его оплачивает `L4_witness` в полную силу — и понадобился бы для линейности шкалы, которую ToS не утверждает.',
  note: DONE + ': было «понадобилась бы… и именно их ToS не проводит». Мост проведён: surjects_injects_back (L4_witness). Теоремы о линейности порядка вложений в формализации нет.' });
set('*Мощность есть роль в предпорядке вложений, а не кардинал-число; антисимметрия и отсутствие максимума доказуемы', { theorem: 'cardinal_antisym_definite', file: CW,
  claim: '*Мощность есть роль в предпорядке вложений, а не кардинал-число; антисимметрия и отсутствие максимума доказуемы без выбора. Выбор не исчезает — он точно локализуется: в переходе от сюръекции к инъекции, где L4 берётся в полную силу, и в линейности кардинальной шкалы, которую ToS оставляет непроведённой.*',
  note: DONE + ': было «в переходе от сюръекции к инъекции и в линейности… которые ToS оставляет непроведёнными». cardinal_antisym_definite — Closed; surjects_injects_back — L4_witness.' });
// пять записей с одной цитатой (сокращённая запись шести имён): одна «имени нет» и четыре по именам
{
  const NEWC = '`surjects_refl`, `surjects_trans`, `bijects_refl`, `bijects_trans`, `bijects_injects`, `bijects_both` — все **0 аксиом**.';
  const hit = j.records.filter((r) => norm(r.claim).startsWith('`surjects_refl/_trans`, `bijects_refl/_trans/_injects/_both`'));
  if (hit.length !== 5) throw new Error('ожидалось пять записей с сокращённой цитатой, найдено ' + hit.length);
  for (const r of hit) {
    r.claim = NEWC; n++;
    if (!r.theorem) Object.assign(r, { theorem: 'surjects_trans', file: CW, page_price: '0 аксиом', verdict: 'ok',
      note: DONE + ': было сокращение «surjects_refl/_trans, bijects_refl/_trans/_injects/_both» — таких объявлений нет; выписаны шесть полных имён. surjects_trans : forall A B C, surjects A B -> surjects B C -> surjects A C. Closed under the global context.' });
  }
  add({ theorem: 'bijects_injects', file: CW, page_price: '0 аксиом', claim: NEWC,
    note: 'bijects_injects : forall A B, bijects A B -> injects A B. Closed under the global context.' });
}
set('признак `B_rooted` решается через `L3_informative` (информативное исключённое третье)', { theorem: 'em_inf', file: SB,
  claim: 'признак `B_rooted` («цепь обрывается в $B$», `B_rooted_iff_B_stops`) решается информативным исключённым третьим `em_inf`. Оно выведено из исключённого третьего и извлечения единственного свидетеля: бит истинности высказывания единствен.',
  note: DONE + ': было «решается через L3_informative — это и есть цена L3» (L3_informative стоит на classic и L4_witness). После шага 1 доказательство использует em_inf : (forall P, P \\/ ~ P) -> (forall T P, (exists! x, P x) -> {x | P x}) -> forall P, {P} + {~ P} — Closed under the global context.' });
set('В самом доказательстве `L4_witness` применяется через производную лемму определённого описания `L4_definite`', { theorem: 'L4_definite', file: 'src/ToS_Axioms.v', page_price: 'classic + L4_witness',
  claim: '`Schroeder_Bernstein` и обёртка `cardinal_antisym` — те же теоремы, в которых посылки заменены на `classic` и `L4_definite` (определённое описание, выведенное из `L4_witness`); для них компилятор называет `classic` ${}+{}$ `L4_witness`.',
  note: DONE + ': было «L4_witness применяется через L4_definite» при втором, неназванном пути через L3_informative. После шага 1 путь один: Schroeder_Bernstein := Schroeder_Bernstein_definite classic (@L4_definite). L4_definite : (exists! x, P x) -> {x | P x}, выведена из L4_witness.' });

add({ theorem: 'Schroeder_Bernstein_definite', file: SB, page_price: '0 допущений (посылки вместо аксиом)',
  claim: 'Это закреплено теоремой `Schroeder_Bernstein_definite`: то же заключение выведено из двух посылок — исключённого третьего и извлечения единственного свидетеля, — и допущений у неё нет.',
  note: 'Новая теорема шага 1. ' + DEF });
add({ theorem: 'cardinal_antisym_definite', file: CW, page_price: '0 аксиом',
  claim: '`cardinal_antisym_definite` (из исключённого третьего и единственного свидетеля как посылок, 0 аксиом)',
  note: 'Новая теорема шага 1: ExcludedMiddle -> UniqueWitness -> forall A B, injects A B -> injects B A -> bijects A B. Closed under the global context.' });
add({ theorem: 'no_maximal_in_injection_order_definite', file: CW, page_price: 'L3 и единственный свидетель',
  claim: 'В порядке вложений то же доказано ценой L3 и единственного свидетеля: вложение $X\\hookrightarrow(X\\to\\mathtt{bool})$ требует решать равенство точек, и тогда над каждым носителем есть строго больший (`no_maximal_in_injection_order_definite`).',
  note: 'Новая теорема шага 1: ExcludedMiddle -> UniqueWitness -> forall X, exists Y, injects X Y /\\ ~ injects Y X. Closed under the global context; при classic и L4_definite — no_maximal_in_injection_order (classic + L4_witness). Прежде страница говорила, что строгости в порядке вложений нет.' });
add({ theorem: 'bijects_sym_definite', file: CW, page_price: '0 аксиом',
  claim: 'Извлечение *единственного* свидетеля обращает *биекцию* (прообразы единственны, `bijects_sym_definite`); к слою произвольной сюръекции оно неприменимо: прообразов там может быть много.',
  note: 'Новая теорема шага 1: UniqueWitness -> forall A B, bijects A B -> bijects B A. Closed under the global context. Что мост не выводится из одного единственного свидетеля, средствами Rocq не проверяется — страница говорит «неприменимо», а не «невыводимо».' });
add({ theorem: 'Schroeder_Bernstein_definite', file: SB, page_price: '0 допущений',
  claim: '`Schroeder_Bernstein_definite` (`SchroederBernstein_ERR.v`) и `cardinal_antisym_definite` (`CardinalityWithoutChoice.v`, эта работа) выводят заключение из двух посылок — исключённого третьего и извлечения *единственного* свидетеля из $\\exists!$ — и допущений не имеют.',
  note: 'Сноска 3 после шага 1. ' + DEF });
add({ theorem: 'surjects_injects_back', file: CW, page_price: 'один L4_witness',
  claim: '`surjects_injects_back` (`CardinalityWithoutChoice.v`): `surjects A B -> injects B A`; `Print Assumptions` — один `L4_witness`.',
  note: 'Сноска 6 после шага 1. surjects_injects_back : forall A B, surjects A B -> injects B A; Axioms: ToS_Axioms.L4_witness.' });
add({ theorem: 'split_iff_choice', file: CW, page_price: '0 аксиом',
  claim: 'Равносильность «у каждой сюръекции есть правая обратная» и выбора функции по семейству — `split_iff_choice`, 0 аксиом.',
  note: 'Сноска 6 после шага 1. split_iff_choice : surjections_split <-> functional_choice. Closed under the global context.' });
add({ theorem: 'bijects_sym_definite', file: CW, page_price: '0 аксиом',
  claim: 'Обращение биекции извлечением единственного свидетеля — `bijects_sym_definite`, 0 аксиом.',
  note: 'Сноска 6 после шага 1. Closed under the global context.' });
add({ theorem: 'l4_statement_gives_functional_choice', file: 'src/settheory/ChoicePriceMap.v', page_price: '',
  claim: 'Тот же ход для произвольного семейства — `l4_statement_gives_functional_choice` (`settheory/ChoicePriceMap.v`).',
  note: 'l4_statement_gives_functional_choice (ChoicePriceMap.v): из утверждения L4_witness (посылкой) — функция выбора по семейству. Closed under the global context.' });

fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part10-ch03.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);

// ---- записи с вердиктом «верно», чьи цитаты изменились вместе со страницей (выявлены relocate) ----
{
  const j2 = JSON.parse(fs.readFileSync(p, 'utf8'));
  let m = 0;
  const fix = (prefix, fields) => {
    const hit = j2.records.filter((r) => norm(r.claim).startsWith(prefix));
    if (hit.length === 0) return;                      // уже исправлено прошлым запуском
    if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
    Object.assign(hit[0], fields); m++;
  };
  fix('Биекция $h$ собирается по этому признаку:', {
    claim: 'Биекция $h$ собирается по первому признаку: на укоренённых в $B$ точках берём частичный обратный $g^{-1}$, иначе — $f$.',
    note: 'Definition h (SchroederBernstein_ERR.v): match em_inf (B_rooted a) with left HBa => g_inv a … | right _ => f a. После шага 1 Части X признак решается em_inf (из исключённого третьего и единственного свидетеля).' });
  fix('Какова аксиомная цена? Ровно `classic` (L3) и `L4_witness` (L4)', { page_price: 'classic (L3) и L4_witness (L4)',
    claim: 'Какова аксиомная цена? По компилятору — `classic` (L3) и `L4_witness` (L4).[^3]',
    note: 'Print Assumptions Schroeder_Bernstein: Classical_Prop.classic, ToS_Axioms.L4_witness — как на странице. Слова «и не аксиома выбора» после шага 1 Части X заменены теоремой Schroeder_Bernstein_definite (см. соседние записи).' });
  fix('L3 входит как разрешимость признака укоренённости; `L4_witness` выбирает', { theorem: 'em_inf', file: SB,
    page_price: 'L3 — разрешимость признака; L4 — только единственный свидетель',
    claim: 'L3 входит как разрешимость признака укоренённости. L4 входит только как извлечение *единственного* свидетеля: прообраза под инъекцией и бита истинности признака.',
    note: DONE + ': было «L4_witness выбирает свидетеля из одного существования; функция по семейству из него выводима… завершённого графа выбора теорема не требует». После шага 1 в доказательстве два извлечения, оба — единственного свидетеля: DD для частичных обратных (f_inv, g_inv) и DD внутри em_inf (бит истинности). Closed under the global context.' });
  fix('Именно в этом канторовском (сюръективном) смысле максимума нет: это *не* строгость', { theorem: 'no_maximal_cardinality', file: CW, page_price: '0 допущений',
    claim: 'В этом канторовском (сюръективном) смысле максимума нет без единого допущения.',
    note: DONE + ': было «это не строгость в инъекционном порядке (инъекция потребовала бы разрешимого равенства)». no_maximal_cardinality — Closed under the global context; строгость в порядке вложений теперь доказана отдельной теоремой (no_maximal_in_injection_order_definite, см. соседнюю запись).' });
  fix('**Что даёт.** Антисимметрия $\\le$ — `cardinal_antisym` (L3${}+{}$L4);', {
    claim: '**Что даёт.** Антисимметрия $\\le$ — `cardinal_antisym` (L3${}+{}$L4) и' });
  fix('В `settheory/CardinalityWithoutChoice.v` (эта работа): `injects`, `surjects`, `bijects`; `injects_refl`, `injects_trans` (предпорядок $\\le$), `surjects_refl/_trans`', {
    claim: 'В `settheory/CardinalityWithoutChoice.v` (эта работа): `injects`, `surjects`, `bijects`; `injects_refl`, `injects_trans` (предпорядок $\\le$), `surjects_refl`, `surjects_trans`, `bijects_refl`, `bijects_trans`, `bijects_injects`, `bijects_both` — все **0 аксиом**.' });
  fix('Аксиомный статус сверен `Print Assumptions`: `Schroeder_Bernstein` и обёртка', { theorem: 'cardinal_antisym', file: CW, page_price: 'classic + L4_witness',
    claim: '`Schroeder_Bernstein` и обёртка `cardinal_antisym` — те же теоремы, в которых посылки заменены на `classic` и `L4_definite`',
    note: 'Print Assumptions cardinal_antisym и Schroeder_Bernstein: Classical_Prop.classic, ToS_Axioms.L4_witness — и только они. После шага 1 Части X обе — частные случаи теорем с посылками (cardinal_antisym_definite, Schroeder_Bernstein_definite).' });
  fix('дают ровно `classic` ${}+{}$ `L4_witness`.', {
    claim: 'для них компилятор называет `classic` ${}+{}$ `L4_witness`.' });
  fix('Документировано в шапке `CardinalityWithoutChoice.v`: переход `surjects`', { theorem: 'surjection_has_section', file: CW, page_price: 'один L4_witness',
    claim: '[^6]: `surjects_injects_back` (`CardinalityWithoutChoice.v`): `surjects A B -> injects B A`;',
    note: DONE + ': было «документировано в шапке: переход есть выбор и здесь не выводится» — шапка была неверна и исправлена. surjection_has_section : (forall b, exists a, f a = b) -> exists g, forall b, f (g b) = b; Print Assumptions — ToS_Axioms.L4_witness; из неё surjects_injects_back.' });
  if (!j2.records.some((r) => r.theorem === 'B_rooted_iff_B_stops')) {
    j2.records.push({ line: 0, theorem: 'B_rooted_iff_B_stops', file: SB, page_price: '', verdict: 'ok',
      claim: 'признак `B_rooted` («цепь обрывается в $B$», `B_rooted_iff_B_stops`)',
      note: 'Новая лемма шага 1: forall A B f g a, B_rooted f g a <-> B_stops f g a — признак файла есть в точности «цепь, прослеженная назад, обрывается в B». Closed under the global context.' });
    m++;
  }
  fs.writeFileSync(p, JSON.stringify(j2, null, 1) + '\n');
  console.log('part10-ch03.json: приведено к новым цитатам и добавлено ' + m);
}
