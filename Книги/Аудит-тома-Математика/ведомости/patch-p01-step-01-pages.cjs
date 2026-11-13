// Часть I, шаг 1, страницы (2026-11-13, слово автора «вноси»): 12 правок главы I.5 внесены; формализация —
// src/foundation/DistinctionCoDefinition.v. Запуск: node patch-p01-step-01-pages.cjs
// (затем tom-links relocate + merge по part01-ch05). Скрипт повторяем: приведённая запись пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть I, шаг 1, слово автора)';
const F = 'src/foundation/';
const CD = F + 'DistinctionCoDefinition.v';
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
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', снято ' + dropped + ', всего ' + j.records.length); },
  };
}
const GIVEN = 'В формализации L2 и L3 — поля записи (exclusive, exhaustive), L4 выводится из них, L1 — рефлексивность равенства, L5 — теорема об уровнях; страница теперь говорит это.';
const a = open('part01-ch05.json');

// 1. стр. 13
a.fix('из структуры записи были выведены законы $L1$–$L5$ (Глава 3);', 'five_laws_from_distinction', {
  claim: 'по структуре записи были прослежены законы $L1$–$L5$ (Глава 3): $L2$ и $L3$ входят в запись двумя её правилами, $L4$ выводится из них теоремой, $L1$ принадлежит равенству, $L5$ — иерархии уровней;',
  note: DONE + ': было «из структуры записи были выведены законы L1–L5». ' + GIVEN });
// 2. стр. 27 (две записи одного места)
const OLD27 = 'вывод $L1$–$L5$ из `Distinction` и вывод $P1$–$P4$ из законов суть формальные теоремы';
const NEW27 = 'законы $L1$–$L5$ и принципы $P1$–$P4$ записаны формальными теоремами (что в них выведено, а что дано самой записью — предмет Глав 3 и 4)';
a.fix(OLD27, 'five_laws_from_distinction', { claim: NEW27,
  note: DONE + ': было «вывод L1–L5 из Distinction и вывод P1–P4 из законов суть формальные теоремы». ' + GIVEN });
a.fix(OLD27, 'four_principles_from_five_laws', { claim: NEW27,
  note: DONE + ': было «вывод P1–P4 из законов суть формальные теоремы». four_principles_from_five_laws — конъюнкция четырёх утверждений без посылок-законов; что в принципах выведено, разбирается в главе I.4 (шаги 5–7 Части I).' });
// 3. стр. 486
a.fix('В Главе 3 законы $L1$–$L5$ были выведены как *теоремы* о произвольной `Distinction`', 'five_laws_from_distinction', {
  claim: 'В Главе 3 законы $L1$–$L4$ были получены как *теоремы* о произвольной `Distinction` — утверждения, которые *держатся* на каждом экземпляре: $L2$ и $L3$ — как сами правила записи, $L4$ — как вывод из них; $L5$ — как теорема об уровнях.',
  note: DONE + ': было «законы L1–L5 были выведены как теоремы о произвольной Distinction». Конъюнкт L5 экземпляра D не содержит. ' + GIVEN });
// 4. стр. 603–622: co_constitution
const CC = 'Lemma co_constitution : forall P : Prop, positive (distinction_of P) = P /\\ negative (distinction_of P) = ~ P (Distinction.v:202); доказательство `intro P. split; reflexivity`. Print Assumptions: Distinction.classic (через distinction_of).';
a.fix('В Rocq-репозитории ToS[^3] есть лемма, носящая имя со-определения:', 'co_constitution', {
  note: DONE + ': блок кода приведён к нынешней формулировке. ' + CC });
a.fix('Её доказательство в репозитории — `split; intro H; eexists; reflexivity`', 'co_constitution', {
  claim: 'Её доказательство в репозитории — `intro P. split; reflexivity` — тривиально, и тривиальность эта показательна: оба равенства верны по определению `distinction_of`, которое само помещает $P$ в поле `positive`, а $\\neg P$ — в поле `negative`.',
  note: DONE + ': было — прежнее доказательство и «предпосылки P и ¬P в нём фактически не используются». ' + CC });
a.fix('Её содержание скромнее: как только пропозиция $P$ дана как объект языка', 'co_constitution', {
  claim: 'Её содержание скромнее: каноническое различение по $P$ одним актом задаёт обе стороны — $P$ и $\\neg P$.',
  note: DONE + ': было — содержание прежней формулировки («выражение ¬P уже синтаксически доступно»). ' + CC });
// 5. стр. 673
a.fix('Он добавляется в файле `LawsFromDistinction.v` — объединяющая теорема `five_laws_from_distinction`', 'five_laws_from_distinction', {
  claim: 'Он добавляется в файле `LawsFromDistinction.v` — объединяющая теорема `five_laws_from_distinction` там подключает иерархический слой, причём $L5$ в ней представлен иррефлексивностью порядка уровней — для всякого уровня, $\\forall l,\\ \\neg(l \\ll l)$, — и от конкретного $D$ не зависит',
  note: DONE + ': было «иррефлексивностью базового уровня». Конъюнкт L5 теоремы (:144) — forall l : Level, ~ (l << l).' });
// 6. стр. 862
a.fix('Если `exclusive` утверждает $\\neg (\\texttt{positive} \\wedge \\texttt{negative})$', null, {
  theorem: 'negative_iff_not_positive', file: CD, page_price: '',
  claim: 'Если `exclusive` утверждает $\\neg (\\texttt{positive} \\wedge \\texttt{negative})$, а `exhaustive` — $\\texttt{positive} \\vee \\texttt{negative}$, то из их совокупности *следует* утверждение $\\texttt{negative} \\leftrightarrow \\neg \\texttt{positive}$:',
  note: DONE + ': было «их совокупность эквивалентна утверждению». Из двух полей равносильность следует без аксиом (negative_iff_not_positive — Closed under the global context); обратно исчерпанность требует назначения стороны — об этом новый абзац ниже.' });
// место 6 таблицы (стр. 1355, 1358): слова страницы не менялись, леммы появились
a.fix('Леммы, разобранные в § 5.3, и теоремы, выведенные в Главе 3 — это формальные результаты', null, {
  theorem: 'negative_iff_not_positive', file: CD,
  note: 'закрыто 13.11 (Часть I, шаг 1): страница не менялась; леммы § 5.3 появились — negative_iff_not_positive, positive_iff_not_negative (DistinctionCoDefinition.v), Closed under the global context.' });
a.fix('Утверждения ToS о со-определении суть формальные теоремы, проверяемые Rocq.', null, {
  theorem: 'sides_codetermined', file: CD,
  note: 'закрыто 13.11 (Часть I, шаг 1): страница не менялась; теоремы о со-определении появились — sides_codetermined, negative_determined_by_positive, positive_determined_by_negative, sides_distinct (DistinctionCoDefinition.v), Closed under the global context.' });
// 9. стр. 1545 (две записи одного места)
const OLD1545 = 'В Главе 6 настоящей части обсуждаются технические аксиомы Rocq, на которые опирается работа с `Distinction`';
const NEW1545 = 'В Главе 6 настоящей части обсуждаются аксиомы формализации: классическая аксиома `classic`, на которую опирается каноническое построение `distinction_of`, и аксиома `L4_witness`, реализующая механизм передачи статуса через E/R/R вместо Аксиомы Выбора.';
a.fix(OLD1545, 'classic', { claim: NEW1545, page_price: 'classic — для distinction_of' }, true);
a.fix(OLD1545, 'L4_witness', { claim: NEW1545, page_price: 'аксиома формализации; о записи Distinction не сказано',
  note: DONE + ': было «технические аксиомы Rocq, на которые опирается работа с Distinction, — classic и L4_witness». Ни одно утверждение о записи Distinction от L4_witness не зависит; classic нужен каноническому построению distinction_of — страница теперь говорит это.' });
// 11. сноска 2: обозначение закона набрано формулой, ссылки на идентификатор L2 больше нет
a.drop('Аналогично `L2`:', 'L2');
// 12. сноска 4
const FN4 = 'Обе эквивалентности оформлены леммами `negative_iff_not_positive` и `positive_iff_not_negative` в файле `DistinctionCoDefinition.v` и доказаны из полей `exclusive` и `exhaustive` без аксиом.';
a.fix('В текущей версии репозитория эти эквивалентности отдельными именованными леммами не оформлены', 'negative_iff_not_positive', {
  claim: FN4, file: CD, page_price: 'без аксиом',
  note: DONE + ': было «самостоятельных лемм в файле пока нет». negative_iff_not_positive : forall D, negative D <-> ~ positive D. Closed under the global context.' });
a.fix('самостоятельных лемм `negative_iff_not_positive` и `positive_iff_not_negative` в файле пока нет.', 'positive_iff_not_negative', {
  claim: FN4, file: CD, page_price: 'без аксиом',
  note: DONE + ': было «самостоятельных лемм в файле пока нет». positive_iff_not_negative : forall D, positive D <-> ~ negative D. Closed under the global context.' });
// ---- новые записи: абзац после двух пунктов (правка 7)
const P7a = 'два правила записи равносильны со-определению *вместе с* назначением стороны (`fields_iff_codefinition_and_assignment`);';
const P7b = 'из одного со-определения следуют несовместность ($L2$), самообоснование ($L4$) и отсутствие третьего (`L2_from_codefinition`, `L4_from_codefinition`, `binarity_from_codefinition`);';
const P7c = 'а утверждение «у всякой со-определённой пары одна из сторон имеет место» равносильно исключённому третьему (`totality_from_codefinition_iff_EM`).';
a.add({ theorem: 'fields_iff_codefinition_and_assignment', file: CD, page_price: 'без аксиом', claim: P7a,
  note: 'fields_iff_codefinition_and_assignment : (~ (p /\\ n) /\\ (p \\/ n)) <-> ((n <-> ~ p) /\\ (p \\/ n)). Closed under the global context.' });
a.add({ theorem: 'L2_from_codefinition', file: CD, page_price: 'без аксиом', claim: P7b,
  note: 'L2_from_codefinition : (n <-> ~ p) -> ~ (p /\\ n). Closed under the global context.' });
a.add({ theorem: 'L4_from_codefinition', file: CD, page_price: 'без аксиом', claim: P7b,
  note: 'L4_from_codefinition — самообоснование из одного со-определения. Closed under the global context.' });
a.add({ theorem: 'binarity_from_codefinition', file: CD, page_price: 'без аксиом', claim: P7b,
  note: 'binarity_from_codefinition : (n <-> ~ p) -> ~ ~ (p \\/ n). Closed under the global context.' });
a.add({ theorem: 'totality_from_codefinition_iff_EM', file: CD, page_price: 'без аксиом', claim: P7c,
  note: 'totality_from_codefinition_iff_EM : (forall p n, (n <-> ~ p) -> p \\/ n) <-> (forall P, P \\/ ~ P). Closed under the global context.' });
// ---- новые записи: сноска 4
const F4a = 'каждая сторона определена другой с точностью до равносильности (`negative_determined_by_positive`, `positive_determined_by_negative`);';
const F4b = 'стороны всякого различения различны (`sides_distinct`);';
const F4c = 'два правила записи независимы, и для со-определения нужны оба (`exclusive_not_from_exhaustive`, `exhaustive_not_from_exclusive`, `codefinition_needs_exclusive`, `codefinition_needs_exhaustive`).';
a.add({ theorem: 'negative_determined_by_positive', file: CD, claim: F4a,
  note: 'negative_determined_by_positive : (positive D1 <-> positive D2) -> (negative D1 <-> negative D2). Closed under the global context.' });
a.add({ theorem: 'positive_determined_by_negative', file: CD, claim: F4a, note: 'Симметрично. Closed under the global context.' });
a.add({ theorem: 'sides_distinct', file: CD, claim: F4b,
  note: 'sides_distinct : forall D, positive D <> negative D. Closed under the global context.' });
a.add({ theorem: 'exclusive_not_from_exhaustive', file: CD, claim: F4c,
  note: 'exclusive_not_from_exhaustive : ~ (forall p n, p \\/ n -> ~ (p /\\ n)). Closed under the global context.' });
a.add({ theorem: 'exhaustive_not_from_exclusive', file: CD, claim: F4c, note: 'Closed under the global context.' });
a.add({ theorem: 'codefinition_needs_exclusive', file: CD, claim: F4c,
  note: 'codefinition_needs_exclusive : exists p n, (p \\/ n) /\\ ~ (n <-> ~ p). Closed under the global context.' });
a.add({ theorem: 'codefinition_needs_exhaustive', file: CD, claim: F4c, note: 'Closed under the global context.' });
a.save();
