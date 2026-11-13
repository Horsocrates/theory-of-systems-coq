// Часть I, шаг 8 (2026-11-13, слово автора «А ; А ; вноси 3 и 4»): одно объявление classic на весь проект;
// объявления раздела Навье — Стокса переведены в посылки (класс NSCoupling); 11 правок главы I.6 внесены
// (правки 2, 4, 8 при этих решениях не понадобились; правка 5 в изменённом виде ждёт слова автора).
// Запуск: node patch-p01-step-08-pages.cjs   (затем relocate + merge по всем ведомостям: имена допущений изменились)
// Скрипт повторяем: приведённая запись пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть I, шаг 8, слово автора)';
const TRUE_NOW = 'закрыто 13.11 (Часть I, шаг 8): страница не менялась, формализация доведена до её слов. Строка `Axiom` в src одна — L4_witness (ToS_Axioms.v:105); classic объявлен один раз, в стандартной библиотеке, и приходит через ToS_Axioms.v (местные объявления в Distinction.v и BorelDeterminacy.v сняты); объявления раздела Навье — Стокса переведены в посылки — запись NSCoupling (GalerkinSystem.v), строк Parameter нет.';
const F = 'src/foundation/';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  return {
    fix(prefix, th, fields, keepVerdict) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) &&
        (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
      if (hit.length === 0) return;
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix.slice(0, 50) + '» / ' + th + ', найдено ' + hit.length);
      Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
    },
    add(rec) {
      if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); },
  };
}
const a = open('part01-ch06.json');

// ---- место 1 и место 12: «два объявления, других нет» — теперь верно буквально
a.fix('Второй слой — два утверждения, объявленные в файле `ToS_Axioms.v`', null, {
  claim: 'Второй слой — два утверждения, на которых стоит логика репозитория: `L4_witness`, объявленный в файле `ToS_Axioms.v` репозитория[^1] как `Axiom`, и `classic`, который тот же файл берёт из стандартной библиотеки Rocq, где он объявлен как `Axiom`.',
  page_price: 'две логические аксиомы: L4_witness (ToS_Axioms.v), classic (стандартная библиотека)',
  note: DONE + ': было «два утверждения, объявленные в файле ToS_Axioms.v как Axiom» — в самом файле строка Axiom одна, classic он реэкспортирует.' });
a.fix('Сейчас существенно одно: *сверх платформы CIC других `Axiom`-объявлений в ToS-Coq нет*.', null, { note: TRUE_NOW });
a.fix('*Всё содержание ToS-репозитория, выходящее за пределы платформы CIC, сводится *логически* к двум законам', null, { note: TRUE_NOW });
a.fix('В репозитории ToS `classic` не объявляется заново.', 'classic', { note: TRUE_NOW });
a.fix('Логически в проекте *два* предполагаемых аксиоматических объявления', null, { note: TRUE_NOW });
a.fix('Поэтому тезис «всё сверх платформы CIC помещается в два объявления» следует понимать', null, { note: TRUE_NOW + ' Абзац стр. 228–245 ещё описывает прежнее состояние; его правка ждёт слова автора.' });
a.fix('Технически же $L3$ зарегистрирован не в одном месте', 'classic', {
  note: 'Страница отстала от формализации: с 13.11 местное объявление `Axiom classic` в Distinction.v (и в BorelDeterminacy.v) снято — оба файла подключают объявление стандартной библиотеки. Правка абзаца стр. 228–245 (в изменённом виде) ждёт слова автора.' }, true);
a.fix('`classic` как `Axiom` в `ToS_Axioms.v`, потому что CIC по умолчанию', null, { note: TRUE_NOW + ' Точное место объявления названо в сноске 3.' });
a.fix('Эти два пути *встречаются* в одной строке кода', null, { note: TRUE_NOW });
a.fix('Точки, в которых требуется объявление `Axiom`, — два места встречи', null, { note: TRUE_NOW });
a.fix('Точнее, через строку `Require Export Coq.Logic.Classical_Prop` в файле `ToS_Axioms.v`', 'classic', { note: TRUE_NOW });
a.fix('Именно поэтому ToS-репозиторий обходится всего двумя техническими объявлениями', 'B_coeff_bounded', {
  note: TRUE_NOW + ' B_coeff_bounded — теперь лемма (TriadicInteraction.v) из поля B_raw_antisym_bounded записи посылок NSCoupling; Closed under the global context.' });
a.fix('Формально аксиомы у ToS есть — два объявления в CIC', null, { note: TRUE_NOW });
a.fix('Этот объём — два объявления, `classic` и `L4_witness`.', null, { note: TRUE_NOW });
a.fix('ToS объявляет в CIC две технические аксиомы.', null, { note: TRUE_NOW });

// ---- место 2
a.fix('$E/R/R$-структура (Глава 4), теоремы $L1$–$L5$ (Глава 3), теоремы $P1$–$P4$ (Глава 4)', null, {
  note: 'закрыто 13.11 (Часть I, шаг 8): фраза не менялась; следом сказано, что закон L3 для произвольной пропозиции принадлежит слою B, а теоремами слоя C о нём являются поле exhaustive построенной записи и L3_binarity.' });
a.fix('Это — определения и доказанные утверждения; они не вводят новых аксиом', 'distinction_of', {
  claim: 'Это — определения и доказанные утверждения; новых законов они не вводят, а работают на двух нижних слоях.', page_price: '',
  note: DONE + ': было «они не вводят новых аксиом» — при том, что Distinction.v объявлял classic собственной строкой; с 13.11 объявление одно, а слова уточнены.' });
a.add({ theorem: 'L3_binarity', file: F + 'BinarityVsTotality.v',
  claim: 'Закон $L3$ для произвольной пропозиции принадлежит слою B; теоремами слоя C о нём являются свойство уже построенной записи (поле `exhaustive`) и отсутствие третьей стороны (`L3_binarity`).',
  note: 'L3_binarity : forall P : Prop, ~ ~ (P \\/ ~ P). Closed under the global context.' });

// ---- место 4
a.fix('Из `classic` как из исходного утверждения в ToS-репозитории выводятся несколько часто употребительных', 'NNPP_from_L3', {
  claim: 'Из `classic` как из исходного утверждения в ToS-репозитории выводятся производные принципы. Это теоремы (не аксиомы); их полезно зафиксировать ещё в настоящем разделе.',
  note: DONE + ': было «несколько часто употребительных… систематически применяемые в дальнейшем коде». NNPP_from_L3 (ToS_Axioms.v:147) в других файлах не применяется.' });

// ---- место 5
a.fix('`L3_informative` *не* требуется для конструкции `distinction_of`', 'distinction_of', {
  claim: '`L3_informative` *не* требуется для конструкции `distinction_of`: как видно из файла `Distinction.v`, `distinction_of` $(P)$ заполняет поле `exhaustive`, живущее в Prop, значением `classic` $P : P \\vee \\neg P$ — пропозициональной дизъюнкцией, а не информативной $\\{P\\}+\\{\\neg P\\}$.',
  note: DONE + ': было «distinction_of (P) живёт в Prop». Запись Distinction — тип в Type; в Prop живёт поле exhaustive.' });

// ---- место 6
a.fix('Принцип $P4$ из Главы 4 — не аксиома, а *теорема*', 'P4_from_L5', {
  claim: 'Принцип $P4$ из Главы 4 — не аксиома: содержательно он выводится из устройства акта различения через цепочку шагов.',
  note: DONE + ': было «не аксиома, а теорема… и эта теорема имеет следствие — завершённая бесконечность как объект структурно невозможна». В теоремы о несовместимости P4 входит посылкой (P4_stage_bounded), следствие доказано при мосте.' });
a.add({ theorem: 'P4_stage_bounded', file: F + 'P4CompletedInfinity.v',
  claim: 'В формализации он записан как свойство актуальности, ограниченной на каждой стадии (`P4_stage_bounded`): для процесса стадий это свойство доказано, а в теоремы о несовместимости оно входит посылкой.',
  note: 'Definition P4_stage_bounded (actual : nat -> nat -> Prop) : Prop (P4CompletedInfinity.v:39).' });

// ---- место 7
a.fix('Аксиома Выбора, требующая для своей формулировки завершённой бесконечности', null, {
  claim: 'Аксиома Выбора, прочитанная как завершённый граф функции выбора, оказывается несовместимой с $P4$ — не по нашему отказу, а по формальному следствию, при том же мосте.',
  note: DONE + ': было «оказывается несовместимой с P4… по строгому формальному следствию» без оговорки о мосте.' });
a.fix('По уже разобранной причине это в ToS не строится: наличие функции выбора', 'completed_graph_contradicts_P4', {
  claim: 'По уже разобранной причине такое чтение в ToS не принимается: граф $\\{(n, f(n)) \\mid n \\in ℕ\\}$ функции $f : ℕ \\to ℕ$, взятый как завершённое целое, несовместим с $P4$ — в той же условной форме, при мосте.[^10]',
  note: DONE + ': было «это в ToS не строится». completed_graph_contradicts_P4 (P4ProhibitsAC.v:108) — при посылке-мосте; Closed under the global context.' });
a.fix('Работа, для которой в классической математике требуется Аксиома Выбора, в ToS выполняется $L5$-механизмом — но', 'AC_on_nat_as_rule', {
  claim: 'Работа, для которой в классической математике требуется Аксиома Выбора, в ToS выполняется $L5$-механизмом там, где каждый член семейства предъявлен конечным списком: для конечных семейств и — как правило, отвечающее на предъявленный индекс, — для семейства, индексированного всем $ℕ$.',
  note: DONE + ': было «но только для конечных семейств». AC_on_nat_as_rule : AC_on_nat (P4ProhibitsAC.v:160) — функция выбора по всему ℕ как правило; Closed under the global context.' });
a.fix('Формальное доказательство несовместимости — в файле `src/foundation/P4ProhibitsAC.v`.', 'ac_completed_graph_contradicts_P4', {
  theorem: 'completed_graph_contradicts_P4', file: F + 'P4ProhibitsAC.v',
  claim: 'Файл `src/foundation/P4ProhibitsAC.v`: теорема `completed_graph_contradicts_P4` — граф всюду определённой функции, прочитанный как завершённое целое (посылка-мост), противоречит $P4$-ограниченности; это верно для любой функции, не только для функции выбора.',
  note: DONE + ': сноска называет теорему и её условие.' });
a.add({ theorem: 'AC_on_nat_as_rule', file: F + 'P4ProhibitsAC.v',
  claim: 'Утверждение `AC_on_nat` о семействе непустых списков этим не опровергается: в том же файле оно доказано (`AC_on_nat_as_rule`).',
  note: 'AC_on_nat_as_rule : AC_on_nat. Closed under the global context.' });

// ---- место 8
a.fix('Эта стратификация встроена в систему типов CIC через универсную иерархию', null, {
  theorem: 'P1_no_self_membership', file: 'src/TheoryOfSystems_Core_ERR.v',
  claim: 'В формализации уровни заданы собственным индуктивным типом меток `Level`, и у порядка на метках нет петель (`P1_no_self_membership`).',
  note: DONE + ': было «Эта стратификация встроена в систему типов CIC через универсную иерархию». Level — индуктивный тип меток (Core_ERR:59), с универсами CIC не связан; P1_no_self_membership : forall L, ~ (L << L) — Closed under the global context.' });

// ---- место 9 (сноска 11)
const FN11 = 'Формальная сторона — в файле `src/foundation/P4ProhibitsImpredicative.v`: условие Рассела, записанное как посылка, ведёт к противоречию при любом отношении принадлежности (`russell_contradiction_without_P1`); собиратель условия по области лежит вне этой области (`russell_collector_escapes`), поэтому область, у которой собиратель есть, не завершена (`russell_requires_completed_totality`).';
a.fix('Формальная проверка — в файле `src/foundation/P4ProhibitsImpredicative.v`, теорема `P4_dissolves_russell`.', 'P4_dissolves_russell', {
  theorem: 'russell_contradiction_without_P1', file: F + 'P4ProhibitsImpredicative.v', claim: FN11,
  note: DONE + ': было «теорема P4_dissolves_russell» — конъюнкция трёх фактов. Названы теоремы, говорящие о конструкции Рассела; все — Closed under the global context.' });
a.add({ theorem: 'russell_collector_escapes', file: F + 'P4ProhibitsImpredicative.v', claim: FN11, note: 'Closed under the global context.' });
a.add({ theorem: 'russell_requires_completed_totality', file: F + 'P4ProhibitsImpredicative.v', claim: FN11, note: 'Closed under the global context.' });
a.add({ theorem: 'P1_no_self_membership', file: 'src/TheoryOfSystems_Core_ERR.v',
  claim: 'Уровневая сторона — `P1_no_self_membership` в файле `src/TheoryOfSystems_Core_ERR.v`.', note: 'Closed under the global context.' });

// ---- место 10 (слово автора: вносить)
const W10 = DONE + ': изменена названная причина — модули не «привносят Аксиому Выбора»: по утверждению их аксиомы совпадают с classic и L4_witness; причина — учёт допущений.';
a.fix('`Coq.Logic.ClassicalDescription` — определение объекта через свойство', 'ClassicalDescription', {
  claim: '`Coq.Logic.ClassicalDescription` — исключённое третье вместе с определённым описанием: извлечением единственного свидетеля.', page_price: '', note: W10 });
a.fix('`Coq.Logic.ClassicalEpsilon` — гильбертовский $\\epsilon$-оператор, выбирающий произвольного свидетеля', 'ClassicalEpsilon', {
  claim: '`Coq.Logic.ClassicalEpsilon` — исключённое третье вместе с неопределённым описанием и построенный на них гильбертовский $\\epsilon$-оператор.', page_price: '', note: W10 });
a.fix('`Coq.Logic.IndefiniteDescription` — неопределённое описание, ещё одна форма выбора.', 'IndefiniteDescription', {
  claim: '`Coq.Logic.IndefiniteDescription` — неопределённое описание.' }, true);
a.fix('В ToS-репозитории эти модули не импортируются. Это не есть запрет в смысле волевого акта', null, {
  claim: 'В ToS-репозитории эти модули не импортируются. Причина не в том, что они сильнее принятого: по утверждению их аксиомы совпадают с `classic` и `L4_witness` (определённое описание — с их следствием `L4_definite`), и всё, что эти модули дают, из двух объявлений ToS выводится.',
  note: W10 });
a.fix('Если бы они были импортированы, в репозитории появилась бы конструкция', null, {
  claim: 'Причина в учёте: импорт добавил бы второе объявление того же утверждения под другим именем, и вывод `Print Assumptions` перестал бы показывать, что теорема стоит именно на `L4_witness`.',
  note: W10 });
a.fix('В комментарии файла `ToS_Axioms.v` соответствующие модули явно отмечены как не используемые — эта отметка есть техническое', null, {
  claim: 'В комментарии файла `ToS_Axioms.v` соответствующие модули явно отмечены как не используемые — эта отметка есть правило учёта, не дополнительный постулат.' }, true);
a.save();
