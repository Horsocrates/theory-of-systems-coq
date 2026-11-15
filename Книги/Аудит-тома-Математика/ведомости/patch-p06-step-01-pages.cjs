// Часть VI, шаг 1, страницы (2026-11-15, слово автора «Вноси»): 6 правок глав VI.1 и VI.2 внесены
// (сноска 14 главы VI.1; определение, сноски 5 и 6 и два места о несчётности главы VI.2).
// Формализация — новый src/process/ProcessNullCovers.v; прежние файлы не менялись.
// Запуск: node patch-p06-step-01-pages.cjs  (затем relocate + merge по part06-ch01, part06-ch02). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 15.11 (Часть VI, шаг 1, слово автора)';
const CL = 'Closed under the global context';
const NC = 'src/process/ProcessNullCovers.v';
const RN = 'src/process/ProcessRationalsNull.v';
const CM = 'src/process/ProcessCantorMeasure.v';
const BS = String.fromCharCode(92);
const CDOT = BS + 'cdot';
const CAP = BS + 'cap';
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

// утверждения нового файла (номера строк — src/process/ProcessNullCovers.v)
const N_NULL = 'Definition null_set (A : RealProcess -> Prop) : Prop := exists lo hi mu, covering_process A lo hi mu /' + BS + ' mu ~~ const_process 0 (:126); covering_process (:120): на каждой стадии n отрезки [lo n k, hi n k] накрывают A (всякая точка множества лежит в одном из них — proc_in_closed, :74), lo n k <= hi n k, и всякая конечная сумма длин <= mu n. ' + CL + '.';
const N_RCP = 'rationals_covering_process : covering_process rational_point (cov_lo enum_Q) (cov_hi enum_Q) half_pow (:289): отрезок вокруг k-й точки нумерации на стадии n имеет полуширину half_pow n * half_pow (S (S k)), то есть длину (1/2)^n·(1/2)^(k+1); сумма первых N длин равна (1/2)^n·(1 − (1/2)^N) (cov_sum). ' + CL + '.';
const N_RCZ = 'rationals_cover_to_zero : half_pow ~~ const_process 0 (:90) — сходимость оценки; покрытие, которое она оценивает, дано теоремой rationals_covering_process (' + NC + '). ' + CL + '.';
const N_RNULL = 'rationals_null : null_set rational_point (:295), где rational_point x := exists q, x ~~ const_process q. ' + CL + '.';
const N_SRN = 'segment_rationals_null : forall c d : Q, null_set (segment_rational_point c d) (:300), где segment_rational_point c d x := exists q, c <= q /' + BS + ' q <= d /' + BS + ' x ~~ const_process q. ' + CL + '.';
const N_CN = 'countable_null : forall (A : RealProcess -> Prop) (e : nat -> Q), (forall x, A x -> exists k, x ~~ const_process (e k)) -> null_set A (:260) — для множества, исчерпанного последовательностью рациональных точек; для семейства произвольных точек-процессов правило не доказано (нужны модули сходимости). ' + CL + '.';
const N_CNULL = 'cantor_null : null_set in_cantor (:536); покрывающий процесс — стадии построения (cantor_covering_process, :521), оценка — cantor_cover_measure. ' + CL + '.';
const N_CMZ = 'cantor_measure_zero : cantor_cover_measure ~~ const_process 0 (:88) — сходимость оценки (2/3)^n; что она есть суммарная длина отрезков стадии — cantor_stage_total (' + NC + '). ' + CL + '.';
const N_CSC = 'cantor_stage_count : forall n, length (cantor_stage n) = Nat.pow 2 n (:429); cantor_stage n — список левых концов отрезков длины third_pow n = 3^-n (:414). ' + CL + '.';
const N_CST = 'cantor_stage_total : forall n, inject_Z (Z.of_nat (length (cantor_stage n))) * third_pow n == cantor_cover_measure n (:438). ' + CL + '.';
const N_SN = 'stage_nested : forall n x, in_stage (S n) x -> in_stage n x (:458). ' + CL + '.';
const N_IC = 'Definition in_cantor (x : RealProcess) : Prop := forall n, in_stage n x (:455); in_stage n x := exists a, In a (cantor_stage n) /' + BS + ' proc_in_closed x a (a + third_pow n) (:452). Множество населено и не тривиально: zero_in_cantor, half_not_in_cantor, cantor_point_in_cantor. ' + CL + '.';
const N_CCP = 'cantor_covering_process : covering_process in_cantor (fun n => list_lo (cantor_stage n)) (fun n => list_hi (cantor_stage n) (third_pow n)) cantor_cover_measure (:521). ' + CL + '.';
const N_CPIC = 'cantor_point_in_cantor : forall dg, in_cantor (cantor_point dg) (:610); cantor_point dg — процесс приближений по коду dg : nat -> bool (true — цифра 2, false — цифра 0); процесс Коши — cantor_point_Cauchy (:614). ' + CL + '.';
const N_CPD = 'cantor_points_distinct : forall dg dg\' i, dg i <> dg\' i -> ~ (cantor_point dg ~~ cantor_point dg\') (:663). ' + CL + '.';
const N_CPNE = 'cantor_points_not_enumerable : ~ exists f : nat -> (nat -> bool), forall dg : nat -> bool, exists n, cantor_point (f n) ~~ cantor_point dg (:687) — равенство точек, а не кодов; по форме то же, что binary_processes_not_enumerable Главы 4.4. ' + CL + '.';
const N_CNEN = 'cantor_not_enumerable_and_null (:698): null_set in_cantor; всякий код называет точку множества, и процесс её Коши; никакая последовательность кодов не называет всех точек. ' + CL + '.';

// ------------------------------------------------------------------ VI.1
{
  const { fix, add, save } = open('part06-ch01');

  // стр. 267: текст страницы не менялся, стал верен
  fix('Мера же Лебега, в процессном прочтении, даёт', 'rationals_cover_to_zero', {
    theorem: 'segment_rationals_null', file: NC,
    note: DONE + ' (формализацией): было — за этими словами стояла только сходимость (1/2)^n. ' + N_SRN + ' Покрытие — rationals_covering_process.' });

  // сноска 14 (правка 1)
  const C14a = 'Доказано, 0 аксиом: вокруг $k$-й точки нумерации на стадии $n$ взят отрезок длины $(1/2)^n' + CDOT + '(1/2)^{k+1}$, всякая конечная сумма длин не превосходит $(1/2)^n$ (`rationals_covering_process`), а эта оценка сходится к нулю (`rationals_cover_to_zero`, `ProcessRationalsNull.v`); отсюда мера нуль рациональных точек отрезка — `segment_rationals_null`.';
  fix('Это доказано как процессное утверждение: суммарная длина покрытия', 'rationals_cover_to_zero', {
    theorem: 'rationals_covering_process', file: NC, claim: C14a, page_price: '0 аксиом',
    note: DONE + ' (формализацией): было «суммарная длина покрытия … ведёт себя как (1/2)^n» при том, что покрытия в формализации не было. ' + N_RCP });
  add({ theorem: 'rationals_cover_to_zero', file: RN, claim: C14a, page_price: '0 аксиом', note: N_RCZ });
  add({ theorem: 'segment_rationals_null', file: NC, claim: C14a, page_price: '0 аксиом', note: N_SRN });
  const C14b = 'Для канторова множества покрытие иное — $2^n$ отрезков стадии $n$ суммарной длины $(2/3)^n$: `cantor_null`, со сходимостью оценки `cantor_measure_zero` (`ProcessCantorMeasure.v`).';
  fix('Тот же приём даёт меру нуль и для канторова множества', 'cantor_measure_zero', {
    theorem: 'cantor_null', file: NC, claim: C14b, page_price: '0 аксиом',
    note: DONE + ' (формализацией): было «тот же приём»; приём иной — не нумерация точек, а стадии из 2^n отрезков. ' + N_CNULL + ' Счёт и сумма длин — cantor_stage_count, cantor_stage_total.' });
  add({ theorem: 'cantor_measure_zero', file: CM, claim: C14b, page_price: '0 аксиом', note: N_CMZ });
  add({ theorem: 'null_set', file: NC, page_price: '0 аксиом',
    claim: 'Покрытия и определение меры нуль — в файле `ProcessNullCovers.v`; оба построения разбирает следующая глава.',
    note: N_NULL + ' Print Assumptions для всех 55 объявлений файла — ' + CL + '.' });

  save();
}

// ------------------------------------------------------------------ VI.2
{
  const { fix, add, save } = open('part06-ch02');

  // стр. 13: мера нуль доведена; «объединения интервалов» остаётся за шагом 2
  fix('Настоящая глава распространяет это правило на сам *процессный континуум*', null, {
    verdict: 'mismatch-statement',
    note: 'Шаг 1 (15.11): множества точек-процессов и два эталонных множества определены, их мера нуль доказана (' + NC + ': null_set, segment_rationals_null, cantor_null). Остаётся «на объединения интервалов»: объединение представлено леммой о двух примыкающих интервалах, для процесса меры аддитивность не доказана — место 2.4, шаг 2.' });

  // стр. 23: список «доказано без аксиом»
  const C23 = 'мера нуль рациональных точек отрезка и канторова множества — как сходимость покрывающего процесса к нулю.';
  fix(C23, 'rationals_cover_to_zero', {
    theorem: 'segment_rationals_null', file: NC,
    note: DONE + ' (формализацией): было — две теоремы о сходимости (1/2)^n и (2/3)^n без покрытий. ' + N_SRN + ' Покрывающий процесс — rationals_covering_process, оценка half_pow ~~ const_process 0.' });
  add({ theorem: 'cantor_null', file: NC, claim: C23, page_price: 'без аксиом', note: N_CNULL });

  // стр. 34: «нуль-покрытия»
  fix('Название главы обозначает *направление* расширения: формально здесь доказаны', null, {
    theorem: 'rationals_covering_process', file: NC,
    note: DONE + ' (формализацией): нуль-покрытия теперь объявлены и доказаны. ' + N_RCP + ' Для канторова множества — cantor_covering_process. Мера интервала и правило накопления — как прежде (measure_interval_eq, sigma_additive_converges).' });

  // стр. 112: определение (правка 2)
  fix('В ToS это и есть определение: не «нижняя грань равна нулю»', 'is_null_set', {
    theorem: 'null_set', file: NC,
    claim: 'В ToS это и есть определение: не «нижняя грань равна нулю» (завершённая операция), а *наличие покрывающего процесса, сходящегося к $0$* (в формализации — определение `null_set`, файл `ProcessNullCovers.v`).',
    note: DONE + ' (формализацией): было — определением служил is_null_set, предикат от числового процесса без множества и покрытия. ' + N_NULL + ' Мост к прежнему предикату — covering_measure_is_null (:173).' });

  // стр. 119: рациональные точки (текст не менялся)
  fix('Тогда $k$-ю точку накрывают интервалом длины, убывающей геометрически', 'rationals_cover_to_zero', {
    theorem: 'segment_rationals_null', file: NC,
    note: DONE + ' (формализацией): было — только сходимость (1/2)^n. ' + N_SRN + ' ' + N_RCP });

  // стр. 130: канторово построение (текст не менялся)
  const C130 = 'на стадии $n$ остаётся $2^n$ отрезков длины $3^{-n}$, суммарной длины $(2/3)^n$. Эта суммарная длина — покрывающий процесс, сходящийся к нулю, поэтому канторово множество имеет меру нуль.[^6]';
  fix('на стадии $n$ остаётся $2^n$ отрезков длины $3^{-n}$, суммарной длины', 'cantor_measure_zero', {
    theorem: 'cantor_null', file: NC,
    note: DONE + ' (формализацией): было — только сходимость (2/3)^n; стадий, отрезков и множества не было. ' + N_CNULL });
  add({ theorem: 'cantor_stage_count', file: NC, claim: C130, page_price: '0 аксиом (сноска 6)', note: N_CSC });
  add({ theorem: 'cantor_stage_total', file: NC, claim: C130, page_price: '0 аксиом (сноска 6)', note: N_CST });

  // абзац о несчётности (правка 5)
  const C133 = 'В процессной линии доказана его *мера нуль* и несчётность в смысле Главы 4.4: всякий код из цифр $0$ и $2$ называет точку множества (`cantor_point_in_cantor`), разные коды называют разные точки (`cantor_points_distinct`), и никакая последовательность кодов не называет их все — диагональный код даёт точку множества, отличную от каждой перечисленной (`cantor_points_not_enumerable`, файл `ProcessNullCovers.v`).';
  fix('В настоящей процессной линии доказана лишь его *мера нуль*', 'cantor_measure_zero', {
    theorem: 'cantor_points_not_enumerable', file: NC, claim: C133,
    note: DONE + ' (формализацией): было «доказана лишь его мера нуль» при том, что и множества в формализации не было. ' + N_CPNE });
  add({ theorem: 'cantor_null', file: NC, claim: C133, note: N_CNULL });
  add({ theorem: 'cantor_point_in_cantor', file: NC, claim: C133, note: N_CPIC });
  add({ theorem: 'cantor_points_distinct', file: NC, claim: C133, note: N_CPD });
  fix('отдельной Rocq-теоремы о мощности именно канторова множества здесь не используется', null, {
    theorem: 'cantor_points_not_enumerable', file: NC,
    claim: 'Мощность континуума остаётся классическим чтением: последовательностей произвольных процессов, не заданных кодами, теорема не касается.',
    note: DONE + ': было «отдельной Rocq-теоремы о мощности именно канторова множества здесь не используется» — теорема появилась. Оговорка верна: в cantor_points_not_enumerable (:687) перечисление есть f : nat -> (nat -> bool), последовательность кодов; о последовательностях произвольных процессов утверждения нет. ' + CL + '.' });

  // «Несчётно — но меры нуль» (правка 6)
  add({ theorem: 'cantor_not_enumerable_and_null', file: NC,
    claim: 'Канторово множество несчётно по первому вопросу и нулево по второму — и то и другое доказано (`cantor_not_enumerable_and_null`).',
    note: DONE + ': было «классически несчётно по первому вопросу и доказуемо нулево по второму». ' + N_CNEN });

  // разбор E/R/R: оговорка об уровне — примечание обновлено
  fix('Оговорка об уровне прежняя: «система меры на континууме»', null, {
    note: 'Записи или структуры «система меры» в названных файлах нет; оговорка верна. Под неё подпадают строки разбора E/R/R (стр. 44–55, 199–222). Правило «счётное => нуль» с шага 1 (15.11) есть теорема: countable_null (' + NC + ':260) — для множества, исчерпанного последовательностью рациональных точек.' });

  // итог главы: мера нуль доведена; растяжение остаётся за шагом 2
  fix('Положительная же часть — ровно та, что доказана: мера интервала и её инвариантность', null, {
    verdict: 'mismatch-statement',
    note: 'Шаг 1 (15.11): меры нуль счётного и канторова множеств доказаны с покрытиями (' + NC + ': countable_null, segment_rationals_null, cantor_null). Доказаны также мера интервала, инвариантность к сдвигу, сходимость частичных сумм. Остаётся растяжение: measure_scale есть mu([0,k]) = k — место 2.3, шаг 2.' });

  // сноска 5 (правка 3)
  const C5a = 'Доказано, 0 аксиом (файл `ProcessNullCovers.v`): вокруг $k$-й точки нумерации на стадии $n$ взят отрезок длины $(1/2)^n' + CDOT + '(1/2)^{k+1}$; всякая рациональная точка накрыта, а всякая конечная сумма длин не превосходит $(1/2)^n$ — `rationals_covering_process`; эта оценка сходится к нулю — `rationals_cover_to_zero` (`ProcessRationalsNull.v`).';
  fix('Доказано: покрывающий процесс $(1/2)^n$ сходится к нулю как процесс', 'rationals_cover_to_zero', {
    theorem: 'rationals_covering_process', file: NC, claim: C5a, page_price: '0 аксиом',
    note: DONE + ' (формализацией): было — слово «покрывающий» теоремой не обеспечивалось. ' + N_RCP });
  add({ theorem: 'rationals_cover_to_zero', file: RN, claim: C5a, page_price: '0 аксиом', note: N_RCZ });
  const C5b = 'Отсюда `rationals_null` и `segment_rationals_null`; общее правило для множества, исчерпанного последовательностью рациональных точек, — `countable_null`.';
  add({ theorem: 'rationals_null', file: NC, claim: C5b, page_price: '0 аксиом', note: N_RNULL });
  add({ theorem: 'segment_rationals_null', file: NC, claim: C5b, page_price: '0 аксиом', note: N_SRN });
  add({ theorem: 'countable_null', file: NC, claim: C5b, page_price: '0 аксиом', note: N_CN });

  // сноска 6 (правка 4)
  const C6a = 'Доказано, 0 аксиом (файл `ProcessNullCovers.v`): стадия $n$ состоит ровно из $2^n$ отрезков длины $3^{-n}$ (`cantor_stage_count`), их суммарная длина равна $(2/3)^n$ (`cantor_stage_total`), стадии вложены (`stage_nested`); множество — точки, лежащие во всех стадиях (`in_cantor`); покрывающий процесс — `cantor_covering_process`, мера нуль — `cantor_null`.';
  fix('Доказано: процесс покрытия $(2/3)^n$ сходится к нулю', 'cantor_measure_zero', {
    theorem: 'cantor_null', file: NC, claim: C6a, page_price: '0 аксиом',
    note: DONE + ' (формализацией): было — слова «процесс покрытия» теоремой не обеспечивались. ' + N_CNULL });
  add({ theorem: 'cantor_stage_count', file: NC, claim: C6a, page_price: '0 аксиом', note: N_CSC });
  add({ theorem: 'cantor_stage_total', file: NC, claim: C6a, page_price: '0 аксиом', note: N_CST });
  add({ theorem: 'stage_nested', file: NC, claim: C6a, page_price: '0 аксиом', note: N_SN });
  add({ theorem: 'in_cantor', file: NC, claim: C6a, page_price: '0 аксиом', note: N_IC });
  add({ theorem: 'cantor_covering_process', file: NC, claim: C6a, page_price: '0 аксиом', note: N_CCP });
  add({ theorem: 'cantor_measure_zero', file: CM, page_price: '0 аксиом',
    claim: 'Оценка $(2/3)^n$ сходится к нулю — `cantor_measure_zero` (`ProcessCantorMeasure.v`).', note: N_CMZ });

  save();
}
