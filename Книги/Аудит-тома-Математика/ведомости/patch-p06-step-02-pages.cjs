// Часть VI, шаг 2, страницы (2026-11-15, слово автора «Да, продолжай»): 9 правок глав VI.1, VI.2, VI.3 внесены
// (VI.1: «три уровня строгости», формальный статус различимости, объём Жордана, сноски 1, 7, 8;
//  VI.2: сноски 1 и 2; VI.3: сноска 6). Формализация — новый src/process/ProcessMeasureIntervals.v;
// прежние файлы не менялись.
// Запуск: node patch-p06-step-02-pages.cjs  (затем relocate + merge по part06-ch01, -ch02, -ch03). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 15.11 (Часть VI, шаг 2, слово автора)';
const CL = 'Closed under the global context';
const MI = 'src/process/ProcessMeasureIntervals.v';
const BS = String.fromCharCode(92);
const AND = '/' + BS;
const OR = BS + '/';
const SIGMA = '$' + BS + 'sigma$';
const MU = BS + 'mu';
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

function open(name) {
  const p = path.join(__dirname, name + '.json');
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0, noted = 0;
  const pick = (prefix, th) => {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
    if (hit.length > 1) throw new Error(name + ': не одна запись: ' + prefix + ' / ' + th);
    return hit[0];
  };
  // правка записи: вердикт ok, если не передан другой
  const fix = (prefix, th, fields) => { const r = pick(prefix, th); if (!r) return; Object.assign(r, { verdict: 'ok' }, fields); n++; };
  // только примечание (вердикт не трогается); запись обязана существовать
  const note = (prefix, th, text) => {
    const r = pick(prefix, th);
    if (!r) throw new Error(name + ': запись для примечания не найдена: ' + prefix + ' / ' + th);
    if (r.note !== text) { r.note = text; noted++; }
  };
  const add = (rec) => {
    if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
    j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
  };
  const save = () => { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + '.json: изменено ' + n + ', примечаний ' + noted + ', добавлено ' + added + ', всего ' + j.records.length); };
  return { j, fix, note, add, save };
}

// утверждения нового файла (номера строк — src/process/ProcessMeasureIntervals.v)
const N_RATE = 'measure_process_rate : forall a b c d n, a < b -> a <= c -> c <= d -> d <= b -> Qabs (PMT.measure_process a b c d n - (d - c)) <= integral_step a b n (:154), где integral_step a b n = (b − a)/(n + 1) — шаг сетки стадии n (process/ProcessIntegral.v:42). ' + CL + '.';
const N_CONV = 'measure_process_converges : forall a b c d, a < b -> a <= c -> c <= d -> d <= b -> PMT.measure_process a b c d ~~ const_process (d - c) (:171); следствие — measure_process_Cauchy (:181). ' + CL + '.';
const N_NOTSUP = 'Стадии не монотонны и бывают больше d − c: measure_process_not_sup (:194) — для [1/3, 2/3] в [0, 1] стадии 1, 2, 3 дают 1/2, 2/3, 1/4; мера читается как предел процесса, а не как верхняя грань стадий.';
const N_SCALE = 'measure_scaling_nonneg : forall k a b (Hk : 0 <= k) (Hab : a <= b), LM.measure_interval (k * a) (k * b) (scale_le k a b Hk Hab) == k * LM.measure_interval a b Hab (:219); то же с явной посылкой k * a <= k * b — measure_scaling (:205). ' + CL + '.';
const N_SHIFT = 'measure_shift_general : forall a b t (Hab : a <= b) (Ht : a + t <= b + t), LM.measure_interval (a + t) (b + t) Ht == LM.measure_interval a b Hab (:227). ' + CL + '.';
const N_CHAIN = 'measure_finite_additive_chain : forall (p : nat -> Q) (Hm : forall k, p k <= p (S k)) n (H0n : p 0 <= p n), q_sum (fun k => LM.measure_interval (p k) (p (S k)) (Hm k)) n == LM.measure_interval (p 0) (p n) H0n (:243) — цепочка из n примыкающих интервалов с узлами p 0 <= p 1 <= … <= p n. ' + CL + '.';
const N_ADDEQ = 'measure_process_additive_equiv : forall a b c d e, a < b -> c <= d -> d <= e -> (fun n => PMT.measure_process a b c d n + PMT.measure_process a b d e n) ~~ PMT.measure_process a b c e (:356). ' + CL + '.';
const N_ADDPT = 'measure_process_additive_upto_point : forall a b c d e n, a < b -> c <= d -> d <= e -> PMT.measure_process a b c d n + PMT.measure_process a b d e n == PMT.measure_process a b c e n + PMT.measure_process a b d d n (:290); добавок — процесс меры точки d: он неотрицателен (measure_process_nonneg, process/ProcessMeasureTheory.v:43) и не больше шага сетки (measure_process_point_le_step, :346). ' + CL + '.';
const N_DIST = 'Definition distinguishable (A : RealProcess -> Prop) : Prop := forall eps, 0 < eps -> exists (l : list (Q * Q)) (lo hi : nat -> Q), (exists b, chain b l) ' + AND + ' (forall k, lo k <= hi k) ' + AND + ' (forall x, sym_diff A l x -> exists k, proc_in_closed x (lo k) (hi k)) ' + AND + ' (forall N, q_sum (fun k => hi k - lo k) N < eps) (:744); sym_diff A l x := (A x ' + AND + ' ~ in_union l x) ' + OR + ' (is_Cauchy x ' + AND + ' in_union l x ' + AND + ' ~ A x) (:736); chain (:387) — упорядоченная цепочка отрезков: следующий начинается не раньше конца предыдущего. ' + CL + '.';
const N_FDIST = 'Definition finitely_distinguishable (A : RealProcess -> Prop) : Prop := forall eps, 0 < eps -> finitely_distinguishable_within A eps (:403); finitely_distinguishable_within A eps (:396): есть цепочки inner и outer, всякая точка Коши из inner лежит в A, всякая точка A лежит в outer, и total_len outer - total_len inner <= eps. Для отрезка — interval_finitely_distinguishable (:438), с числом d − c между оценками — interval_has_content (:425). ' + CL + '.';
const N_SEGD = 'segment_distinguishable : forall c d, c <= d -> distinguishable (fun x => proc_in_closed x c d) (:768). ' + CL + '.';
const N_RATD = 'segment_rationals_distinguishable : forall c d : Q, distinguishable (segment_rational_point c d) (:781) — через null_set_distinguishable (:753): всякое множество меры нуль различимо. ' + CL + '.';
const N_CAND = 'cantor_distinguishable : distinguishable in_cantor (:787) — через null_set_distinguishable (:753) и cantor_null (src/process/ProcessNullCovers.v). ' + CL + '.';
const N_IRR = 'segment_has_irrational_point : forall p q : Q, p < q -> exists y : RealProcess, is_Cauchy y ' + AND + ' proc_in_closed y p q ' + AND + ' ~ rational_point y (:673) — точка построена трисекционной диагональю против нумерации рациональных enum_Q (diagonal_point_avoids, :648). ' + CL + '.';
const N_LOWER = 'chain_cover_lower_bound : forall l lo c d, chain lo l -> (forall q : Q, c < q -> q < d -> in_union l (const_process q)) -> d - c <= total_len l (:499) — цепочка отрезков, накрывшая рациональные точки (c, d), имеет суммарную длину не меньше d − c. ' + CL + '.';
const N_NOTFD = 'segment_rationals_not_finitely_distinguishable : forall c d : Q, c < d -> ~ finitely_distinguishable (segment_rational_point c d) (:715): внутренняя цепочка, все точки Коши которой рациональны, имеет суммарную длину <= 0 (rational_chain_degenerate, :691 — в отрезке положительной длины есть иррациональная точка), внешняя не короче d − c (chain_cover_lower_bound, :499). Сводная теорема — rationals_distinguishable_not_finitely (:793): мера нуль, различимо, конечно — неразличимо. ' + CL + '.';

// ------------------------------------------------------------------ VI.1
{
  const { fix, note, add, save } = open('part06-ch01');

  // правка 1: «три уровня строгости» (место 1.1)
  const C1 = '*Второй* — процессные *чтения* меры и ' + SIGMA + '-аддитивности (мера интервала как предел процесса приближений, сходимость частичных сумм): доказаны именно эти процессные утверждения — первое без аксиом, второе при явно названной цене (L3).';
  fix('*Второй* — процессные *чтения* меры и ' + SIGMA + '-аддитивности (мера как sup-процесс', 'measure_process', {
    theorem: 'measure_process_converges', file: MI, claim: C1, page_price: 'без аксиом',
    note: DONE + ': было «мера как sup-процесс … при явно названной цене (L3)» — о процессе меры были доказаны только неотрицательность, оценка сверху и монотонность по включению. ' + N_CONV + ' ' + N_RATE + ' ' + N_NOTSUP });
  add({ theorem: 'sigma_additive_converges', file: 'src/process/ProcessSigmaAdditive.v', claim: C1, page_price: 'L3',
    note: 'Второе из двух утверждений фразы: sigma_additive_converges (:98) — при mu k >= 0 и ограниченных частичных суммах процесс partial_measure mu есть is_Cauchy. Print Assumptions: Classical_Prop.classic.' });

  // правка 2: § «Измеримое есть различимое», формальный статус
  const C2 = 'Сам предикат записан отдельно (`distinguishable`, файл `ProcessMeasureIntervals.v`): множество совпадает с конечным набором отрезков с точностью до покрытия сколь угодно малой суммарной длины; доказано, что различимы отрезок, рациональные точки отрезка и канторово множество.';
  add({ theorem: 'distinguishable', file: MI, claim: C2,
    note: DONE + ' (добавлено): ' + N_DIST + ' Не доказано: что конечная различимость влечёт общую (доказано для отрезка), пример неразличимого множества.' });
  add({ theorem: 'segment_distinguishable', file: MI, claim: C2, note: N_SEGD });
  add({ theorem: 'segment_rationals_distinguishable', file: MI, claim: C2, note: N_RATD });
  add({ theorem: 'cantor_distinguishable', file: MI, claim: C2, note: N_CAND });
  note('В коде этот тезис реализован пока на базовом интервальном/ступенчатом уровне', null,
    'Статус назван честно: в файле есть characteristic_step (:56) и measure_interval (:72) для интервала; общего предиката измеримости в LebesgueMeasure.v нет (слова «measurability = distinguishability» стоят в шапке и в заключительном комментарии). С 15.11 (шаг 2) предикат записан отдельно — distinguishable (' + MI + ':744); страница говорит об этом в конце абзаца.');

  // правка 3: § «Мера Лебега против объёма Жордана»
  const C3a = 'По Жордану оно *неизмеримо*: изнутри его не накрыть ни одним интервалом положительной длины (между любыми двумя рациональными есть иррациональный процесс, точку которого рациональные не заполняют), а снаружи конечными интервалами меньше всей длины $d-c$ не накрыть.';
  const C3b = 'Внутренняя и внешняя оценки не сходятся — объём Жордана не определён (`segment_rationals_not_finitely_distinguishable`, файл `ProcessMeasureIntervals.v`).';
  add({ theorem: 'segment_has_irrational_point', file: MI, claim: C3a,
    note: 'Довод «изнутри»: ' + N_IRR + ' До шага 2 (15.11) утверждения об иррациональной точке в каждом отрезке в src не было; текст страницы не менялся.' });
  add({ theorem: 'chain_cover_lower_bound', file: MI, claim: C3a, note: 'Довод «снаружи»: ' + N_LOWER });
  add({ theorem: 'segment_rationals_not_finitely_distinguishable', file: MI, claim: C3b,
    note: DONE + ' (добавлено имя теоремы): ' + N_NOTFD });

  // правка 4: сноска 1, число (место 1.5)
  fix('Опорные файлы — `LebesgueMeasure.v` (каталог `src/analysis/` Rocq-репозитория ToS,', null, {
    claim: 'Опорные файлы — `LebesgueMeasure.v` (каталог `src/analysis/` Rocq-репозитория ToS, 22 доказанных утверждения, 0 `Admitted`, 0 аксиом)',
    note: DONE + ': было «20 доказанных утверждений». В файле 22 строки «Qed.» (grep -c \'Qed' + BS + '.\'); число 20 стоит в устаревшей шапке файла (:5). Из 22 шесть — вспомогательные неравенства между числами (le_0_1 … le_0_0). «0 Admitted» и «0 аксиом» верны.' });

  // правка 5: сноска 7 — цепочка
  add({ theorem: 'measure_finite_additive_chain', file: MI,
    claim: 'Для цепочки из $n$ примыкающих интервалов аддитивность доказана отдельно — `measure_finite_additive_chain` (файл `ProcessMeasureIntervals.v`).',
    note: DONE + ' (добавлено): ' + N_CHAIN });
  note('Это *базовый случай* конечной аддитивности; общая аддитивность для произвольного списка', 'measure_additive',
    'Статус назван честно: measure_additive (:140) — два примыкающих интервала; char_adjacent_sum (:198) — то же для списков из двух ступеней; утверждения о списке непересекающихся интервалов в файле нет. С 15.11 (шаг 2) цепочка из n примыкающих интервалов доказана — measure_finite_additive_chain (' + MI + ':243, сноска 7); произвольный список непересекающихся интервалов остаётся расширением.');

  // правка 6: сноска 8 (место 1.2)
  const C8a = 'В `ProcessMeasureTheory.v`: `measure_process` (процесс индикатора), `q_measure_additive`, `q_measure_monotone`, а также внешние оценки и предикаты множества меры нуль.';
  const C8b = 'В файле `ProcessMeasureIntervals.v`: процесс меры интервала сходится к $d-c$, отступая от него на каждой стадии не более чем на один шаг сетки (`measure_process_rate`, `measure_process_converges`);';
  const C8c = 'различимость множества — `distinguishable` (множество совпадает с конечным набором отрезков с точностью до покрытия сколь угодно малой суммарной длины), её конечный уровень — `finitely_distinguishable` (множество зажато между внутренним и внешним конечными наборами отрезков).';
  const P8 = 'В `ProcessMeasureTheory.v`: `measure_process` (процесс индикатора), `q_measure_additive`, `q_measure_monotone`,';
  fix(P8, 'measure_process', { claim: C8a,
    note: 'Definition measure_process (a b c d : Q) : RealProcess := indicator_process a b c d (:39) — процесс сумм Римана индикатора [c,d] по сетке из n+1 клеток на [a,b] (ProcessSimple.v:218). Сходимость этого процесса к d − c — measure_process_converges (' + MI + ':171), названа в той же сноске.' });
  fix(P8, 'q_measure_additive', { claim: C8a });
  fix(P8, 'q_measure_monotone', { claim: C8a });
  fix('предикат различимости на стадии $n$ `measurable_at`', 'measurable_at', {
    theorem: 'distinguishable', file: MI, claim: C8c,
    note: DONE + ': было «предикат различимости на стадии $n$ `measurable_at`» — measurable_at (process/ProcessMeasureTheory.v:139) есть функция со значением 0 или 1 по одному биту, не зависящая ни от отрезка, ни от точки; со страниц имя снято, в файле оно оставлено как было. ' + N_DIST });
  add({ theorem: 'finitely_distinguishable', file: MI, claim: C8c, note: N_FDIST });
  add({ theorem: 'measure_process_rate', file: MI, claim: C8b, note: DONE + ' (добавлено): ' + N_RATE });
  add({ theorem: 'measure_process_converges', file: MI, claim: C8b, note: N_CONV + ' ' + N_NOTSUP });

  save();
}

// ------------------------------------------------------------------ VI.2
{
  const { fix, note, add, save } = open('part06-ch02');

  // стр. 13: текст страницы не менялся
  fix('Настоящая глава распространяет это правило на сам *процессный континуум*', null, {
    note: DONE + ' (формализацией; текст страницы не менялся). Шаг 1: множества точек-процессов и два эталонных множества определены, их мера нуль доказана (src/process/ProcessNullCovers.v: null_set, segment_rationals_null, cantor_null). Шаг 2: объединение интервалов — конечная цепочка отрезков (chain, in_union, total_len; ' + MI + ' :387, :383, :379); аддитивность по цепочке из n примыкающих интервалов — measure_finite_additive_chain (:243); для процесса меры — measure_process_additive_equiv (:356). Теоремы «объём объединения цепочки равен сумме длин» как отдельного утверждения нет: суммарная длина цепочки total_len входит в определения различимости; единственность объёма не доказана — горизонт.' });

  // стр. 22 и 59: текст страницы не менялся, стал верен (место 2.3)
  fix('*Доказано без аксиом*: мера интервала и её инвариантность к сдвигу и масштабу;', 'measure_scale', {
    theorem: 'measure_scaling_nonneg', file: MI,
    note: DONE + ' (формализацией; текст страницы не менялся): было — measure_scale (analysis/LebesgueMeasure.v:172) есть measure_interval 0 k H == k, то есть мера отрезка [0, k]. ' + N_SCALE + ' Сдвиг: measure_translation (analysis/LebesgueMeasure.v:179) и ' + N_SHIFT });
  fix('Она зависит *только от ширины*, а не от положения: сдвиг интервала вдоль континуума меру не меняет, а растяжение', 'measure_scale', {
    theorem: 'measure_scaling_nonneg', file: MI,
    note: DONE + ' (формализацией; текст страницы не менялся, сноска 1 продолжена): было — о растяжении произвольного интервала утверждения не было. ' + N_SCALE + ' Сдвиг — measure_translation (analysis/LebesgueMeasure.v:179), measure_shift_general (:227).' });

  // стр. 77: основной текст, примечание
  note('Для *конечного* набора непересекающихся интервалов мера объединения есть сумма мер;', 'measure_additive',
    'measure_additive (:140): measure_interval a b Hab + measure_interval b c Hbc == measure_interval a c Hac. Страница сама называет доказанным только базовый случай. С 15.11 (шаг 2) цепочка из n примыкающих интервалов доказана — measure_finite_additive_chain (' + MI + ':243, названа в сноске 2); объединение как множество точек — in_union для цепочки отрезков (:383).');

  // стр. 98: основной текст, примечание
  note('Причина проста: измеримость у нас уже определена иначе — как различимость,', null,
    'Мера как интеграл индикатора — measure_interval (analysis/LebesgueMeasure.v:72), для интервалов. С 15.11 (шаг 2) предикат различимости записан: distinguishable (' + MI + ':744) — множество совпадает с конечной цепочкой отрезков (то есть его индикатор со ступенчатой функцией) с точностью до покрытия сколь угодно малой суммарной длины; уровень объёма Жордана — finitely_distinguishable (:403). Мера произвольного различимого множества как число не определена — см. заметки, сомнительное место 1.');

  // стр. 241: сводка главы, текст не менялся
  fix('Положительная же часть — ровно та, что доказана: мера интервала и её инвариантность,', null, {
    note: DONE + ' (формализацией; текст страницы не менялся). Шаг 1: меры нуль счётного и канторова множеств доказаны с покрытиями (src/process/ProcessNullCovers.v: countable_null, segment_rationals_null, cantor_null). Шаг 2: инвариантность к растяжению — measure_scaling_nonneg (' + MI + ':219), к сдвигу — measure_translation, measure_shift_general (:227); накопление меры — measure_finite_additive_chain (:243) для цепочки и sigma_additive_converges (process/ProcessSigmaAdditive.v:98, на classic) для счётного набора.' });

  // правка 7: сноска 1
  const C21 = 'Растяжение и сдвиг произвольного интервала — `measure_scaling_nonneg`: $' + MU + '([ka,kb])=k' + BS + ',' + MU + '([a,b])$ при $k' + BS + 'ge 0$, и `measure_shift_general`: $' + MU + '([a+t,b+t])=' + MU + '([a,b])$ (файл `ProcessMeasureIntervals.v`, 0 аксиом).';
  add({ theorem: 'measure_scaling_nonneg', file: MI, claim: C21, page_price: '0 аксиом', note: DONE + ' (добавлено): ' + N_SCALE });
  add({ theorem: 'measure_shift_general', file: MI, claim: C21, page_price: '0 аксиом', note: N_SHIFT });
  note('`measure_scale`: $' + MU + '([0,k])=k$.', 'measure_scale',
    'Lemma measure_scale (:172): forall k (H : 0 <= k), measure_interval 0 k H == k. Формула сноски совпадает с утверждением. Растяжение произвольного интервала — measure_scaling_nonneg (' + MI + ':219), названо в продолжении сноски (15.11). ' + CL + '.');

  // правка 8: сноска 2
  const C22a = 'цепочка из $n$ примыкающих интервалов — `measure_finite_additive_chain`.';
  const C22b = 'Процессный аналог — `measure_process_additive_equiv`: сумма процессов мер $[c,d]$ и $[d,e]$ называет ту же точку, что процесс меры $[c,e]$; на каждой стадии они расходятся не более чем на один шаг сетки — общая точка $d$ сосчитана дважды (`measure_process_additive_upto_point`).';
  fix('процессный аналог — `q_measure_additive` в `ProcessMeasureTheory.v`.', 'q_measure_additive', {
    theorem: 'measure_process_additive_equiv', file: MI, claim: C22b, page_price: '0 аксиом',
    note: DONE + ': было «процессный аналог — `q_measure_additive`» — это тождество о числе d − c (доказательство ring), а не о процессе меры. ' + N_ADDEQ });
  add({ theorem: 'measure_process_additive_upto_point', file: MI, claim: C22b, page_price: '0 аксиом', note: N_ADDPT });
  add({ theorem: 'measure_finite_additive_chain', file: MI, claim: C22a, page_price: '0 аксиом',
    note: DONE + ' (добавлено): ' + N_CHAIN + ' Объявлена в ' + MI + ' (в сноске файл назван в конце: «Обе теоремы — в файле `ProcessMeasureIntervals.v`» — все три имени сноски из этого файла).' });

  save();
}

// ------------------------------------------------------------------ VI.3
{
  const { fix, add, save } = open('part06-ch03');

  // правка 9: сноска 6 (место 3.5)
  const C36a = 'Для множеств различимость записана предикатом `distinguishable` (файл `ProcessMeasureIntervals.v`): множество совпадает с конечным набором отрезков — то есть его индикатор со ступенчатой функцией — с точностью до покрытия сколь угодно малой суммарной длины.';
  const C36b = 'Для функций ту же роль несёт интегрируемость (§ «Интегрируемая функция как предел ступенчатых»); отдельный тип «прообраз-измеримой функции» в текущем корпусе не строится и подаётся как классическое сравнение.';
  fix('Процессный предикат различимости функции на стадии $n$ — `measurable_at`', 'measurable_at', {
    theorem: 'distinguishable', file: MI, claim: C36a,
    note: DONE + ': было «Процессный предикат различимости функции на стадии $n$ — `measurable_at`» — measurable_at (process/ProcessMeasureTheory.v:139) есть функция со значением 0 или 1 по одному биту, не предикат и не о функции. ' + N_DIST });
  add({ theorem: null, file: null, claim: C36b,
    note: 'Типа прообраз-измеримой функции в src нет — верно. Интегрируемость — тип L1Process (analysis/L1Space.v); о его состоянии — записи к стр. 97 и 100 (шаг 3). Предиката различимости для функций в src нет; страница так и говорит.' });

  save();
}
