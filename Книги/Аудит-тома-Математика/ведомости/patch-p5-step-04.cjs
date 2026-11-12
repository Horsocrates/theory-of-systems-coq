// Часть V, шаг 4 (2026-11-12, слово автора «Да — вносим 12 мест и строку 13»): полнота пространства классов.
// Правит ведомости глав V.1, IV.2 и сводной страницы «Формализация».
// Запуск: node patch-p5-step-04.cjs   (затем tom-links.cjs relocate + merge по трём ведомостям)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 4, слово автора)';
const RC = 'src/RealPointComplete.v';
const norm = (s) => (s || '').replace(/\s+/g, ' ');

function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  return {
    j,
    set(prefix, fields) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
      Object.assign(hit[0], fields); n++;
    },
    add(rec) {
      if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, file: RC, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); },
  };
}

// ---------- глава V.1 ----------
const a = open('part05-ch01.json');
a.set('Понятие `is_complete_metric` введено — но ни к одному пространству', {
  note: 'Верно: вне MetricSpace.v предикат нигде не применён. После шага 4 (12.11) имя упомянуто ещё в шапке RealPointComplete.v — в оговорке, что к паре (RealPoint, rp_dist) предикат буквально не применяется (расстояние там — точка, а предикат записан для d : X -> X -> Q).' });
a.set('Применение этого понятия к конкретному процессному пространству', {
  theorem: null, file: RC,
  claim: 'Теоремой полнота стала вне этих файлов и для одного пространства — классов `RealPoint`: без допущений для регулярных представителей, на $L4$ для произвольных.',
  page_price: 'без допущений — для регулярных представителей; L4 — для произвольных',
  verdict: 'ok',
  note: DONE + ': было «Применение этого понятия к конкретному процессному пространству … в опорных файлах главы не проведено и честно оставлено направлением» (статус был честен). Шагом 4 создан src/RealPointComplete.v: regular_class_complete — Closed under the global context; class_complete_L4 — в допущениях только ToS_Axioms.L4_witness. Раздел переписан: понятие is_complete_metric остаётся понятием, теорема названа с ценой, полнота пространства процессов с process_dist оставлена направлением.' });
a.set('Полная метрическая полнота пространства этих классов — не доказана', {
  theorem: null, file: RC,
  claim: 'Полнота пространства этих классов в семи файлах *этой главы* не доказывается — но в репозитории она доказана (файл `RealPointComplete.v`: `regular_class_complete` без допущений, `class_complete_L4` на $L4$); см. § 1.6.',
  page_price: 'regular_class_complete — без допущений; class_complete_L4 — L4',
  verdict: 'ok',
  note: DONE + ': было «Полная метрическая полнота пространства этих классов — не доказана; полнота введена как понятие». Цена обеих теорем сверена Print Assumptions (записи к § 1.6).' });
a.set('Открытым остаётся лишь следующий слой — метрическая *полнота*', {
  theorem: null, file: RC,
  claim: 'Закрыт и следующий слой — метрическая *полнота* пространства классов: она доказана в `RealPointComplete.v` (§ 1.6).',
  verdict: 'ok',
  note: DONE + ': было «Открытым остаётся лишь следующий слой — метрическая полнота пространства классов». Пробное доказательство помощника перенесено в src/RealPointComplete.v и собрано в общей сборке (2042 из 2042).' });
a.set('Открытыми остаются *полная метрическая полнота* пространства этих классов', {
  theorem: null, file: RC,
  claim: 'Доказана и *метрическая полнота* пространства этих классов — в `RealPointComplete.v`: без допущений для регулярных представителей, на $L4$ для произвольных. Открытым остаётся реифицированный фактор-тип отдельным объектом — его ToS не строит сознательно, по $P4$ (Глава 4.3).',
  page_price: 'без допущений — для регулярных представителей; L4 — для произвольных',
  verdict: 'ok',
  note: DONE + ': было «Открытыми остаются полная метрическая полнота … (полнота введена как понятие, не как доказанная теорема) и реифицированный фактор-тип». Фактор-типа в src по-прежнему нет — статус честен.' });
// новые записи: имена нового подраздела § 1.6
a.add({ theorem: 'regular_class_complete',
  claim: 'Если представители регулярны — скорость сходимости каждого известна заранее (`is_Regular_Cauchy`), — рубеж вычисляется, и теорема `regular_class_complete` не опирается ни на одно допущение.',
  page_price: 'ни одного допущения',
  note: 'Новый текст шага 4. Формулировка: forall s : nat -> RealPoint, (forall k, is_Regular_Cauchy (cs_seq (s k))) -> class_cauchy s -> exists L : RealPoint, class_limit s L; рубеж idx k = k + 1 (S), остаток хвоста 2/(k+1). Print Assumptions: Closed under the global context.' });
a.add({ theorem: 'class_complete_L4',
  claim: 'теорема `class_complete_L4` стоит на `L4_witness`, применённом к счётному семейству точек, и только на нём; `classic` ей не нужен.',
  page_price: 'только L4_witness; classic не нужен',
  note: 'Новый текст шага 4. Формулировка: forall s : nat -> RealPoint, class_cauchy s -> exists L : RealPoint, class_limit s L; рубеж k-й точки — proj1_sig (L4_witness … (cs_cauchy (s k) (1/(k+1)) …)), по одному применению на каждое k. Print Assumptions: только ToS_Axioms.L4_witness.' });
a.add({ theorem: 'class_cauchy_compat',
  claim: 'Обе записи корректны на классах: замена представителей их не меняет (`class_cauchy_compat`, `class_limit_compat`).',
  note: 'Новый текст шага 4. (forall k, s k ~~ s\' k) -> class_cauchy s -> class_cauchy s\'; Closed under the global context.' });
a.add({ theorem: 'class_limit_compat',
  claim: 'замена представителей их не меняет (`class_cauchy_compat`, `class_limit_compat`)',
  note: 'Новый текст шага 4. (forall k, s k ~~ s\' k) -> L ~~ L\' -> class_limit s L -> class_limit s\' L\'; Closed under the global context.' });
a.add({ theorem: 'diag_idx_converges',
  claim: 'Диагональный процесс есть процесс Коши и служит пределом (`diag_idx_converges`).',
  note: 'Новый текст шага 4. Секция DiagonalCore: при рубежах idx (хвост k-й точки после idx k уходит не дальше r k), r k -> 0 и class_cauchy s — diag_idx_is_cauchy (диагональ k |-> s k (idx k) есть процесс Коши) и diag_idx_converges : class_limit s diag_idx_limit; Closed under the global context.' });
a.save();

// ---------- глава IV.2 ----------
const b = open('part04-ch02.json');
b.set('полная метрическая полнота пространства классов `CauchySeq` — отдельная задача', {
  theorem: 'regular_class_complete', file: RC,
  claim: 'полная метрическая полнота пространства классов `CauchySeq` доказана отдельно, за пределами Главы 4.2, — в файле `RealPointComplete.v` (Глава 5.1): без допущений для регулярных представителей, на $L4$ для произвольных.',
  page_price: 'без допущений — для регулярных представителей; L4 — для произвольных',
  verdict: 'ok',
  note: DONE + ': было «полная метрическая полнота пространства классов CauchySeq — отдельная задача, выходящая за пределы Главы 4.2» (статус был честен). Шагом 4 Части V создан src/RealPointComplete.v: regular_class_complete — Closed under the global context; class_complete_L4 — только ToS_Axioms.L4_witness.' });
b.add({ theorem: 'class_complete_L4',
  claim: 'без допущений для регулярных представителей, на $L4$ для произвольных.',
  page_price: 'L4',
  note: 'Шаг 4 Части V: вторая из двух теорем, названных фразой (произвольные представители). Print Assumptions: только ToS_Axioms.L4_witness.' });
b.save();

// ---------- сводная страница «Формализация» ----------
const c = open('sverka-2026-11-12/Формализация.json');
c.add({ theorem: 'regular_class_complete',
  claim: '`regular_class_complete`; `class_complete_L4` (RealPointComplete.v) | нет — для регулярных представителей; извлечение свидетеля — для произвольных |',
  page_price: 'нет — для регулярных представителей',
  note: 'Строка внесена шагом 4 Части V (12.11, слово автора). Print Assumptions: Closed under the global context.' });
c.add({ theorem: 'class_complete_L4',
  claim: '`class_complete_L4` (RealPointComplete.v) | нет — для регулярных представителей; извлечение свидетеля — для произвольных |',
  page_price: 'извлечение свидетеля — для произвольных',
  note: 'Строка внесена шагом 4 Части V (12.11, слово автора). Print Assumptions: только ToS_Axioms.L4_witness.' });
c.save();
