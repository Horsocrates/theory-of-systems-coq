// Часть III, шаг 4, страницы (2026-11-14, слово автора «Вноси»): 15 правок главы III.4 внесены.
// Формализация — новый src/Sqrt2Processes.v; прежние файлы не менялись.
// Запуск: node patch-p03-step-04-pages.cjs  (затем relocate + merge по part03-ch04). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 14.11 (Часть III, шаг 4, слово автора)';
const CL = 'Closed under the global context';
const SP = 'src/Sqrt2Processes.v';
const SI = 'src/ShrinkingIntervals_ERR.v';
const BS = String.fromCharCode(92);
const AND = '/' + BS;
const SQ = '$' + BS + 'sqrt{2}$';
const LE = BS + 'le';
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

// утверждения нового файла (номера строк — src/Sqrt2Processes.v)
const S_SQ = 'sq_to_2 R := forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> Qabs (R n * R n - 2) < eps';
const N_GIVES = 'Definition gives_sqrt2 (R : nat -> Q) : Prop := PC.is_Cauchy R ' + AND + ' sq_to_2 R (:127) — предикат в записи страницы; ' + S_SQ + '. ' + CL + '.';
const N_POS = 'Definition gives_pos_sqrt2 (R : nat -> Q) : Prop := (forall n, 0 <= R n) ' + AND + ' sq_to_2 R (:131). ' + CL + '.';
const N_OPP = 'gives_sqrt2_opp : forall R, gives_sqrt2 R -> gives_sqrt2 (fun n => - R n) (:232); что R и −R не эквивалентны — pos_not_equiv_opp, сводно page_predicate_two_classes. ' + CL + '.';
const N_CAU = 'pos_sqrt2_Cauchy : forall R : nat -> Q, gives_pos_sqrt2 R -> PC.is_Cauchy R (:193). ' + CL + '.';
const N_UNI = 'pos_sqrt2_unique : forall R S : nat -> Q, gives_pos_sqrt2 R -> gives_pos_sqrt2 S -> PC.process_equiv R S (:170). ' + CL + '.';
const N_NQB = 'newton_quality_bound : forall n, Qabs (sqrt2_newton n * sqrt2_newton n - 2) * SI.Qpow2 n <= 1 (:361). ' + CL + '.';
const N_NSI = 'newton_strictly_improves : forall n, sqrt2_quality (sqrt2_newton (S n)) < sqrt2_quality (sqrt2_newton n) (:410). ' + CL + '.';
const N_BIS = 'Definition sqrt2_bisect : nat -> Q := SI.bisect_process sqrt2_choose sqrt2_start (:441); половина выбирается сравнением квадрата середины с двойкой (sqrt2_choose, Qle_bool) — без ссылки на цель. ' + CL + '.';
const N_BISC = 'sqrt2_bisect_Cauchy : SI.is_Cauchy sqrt2_bisect (:445); что этот процесс даёт корень — sqrt2_bisect_gives_pos_sqrt2, с оценкой |m_n^2 − 2| <= 4/2^n (sqrt2_bisect_quality). ' + CL + '.';
const N_SIC = 'shrinking_interval_Cauchy : forall (R : RealProcess) (a b : Q), a < b -> (forall m n, (m <= n)%nat -> Qabs (R m - R n) <= (b - a) / Qpow2 m) -> is_Cauchy R. ' + CL + '.';

{
  const { fix, add, save } = open('part03-ch04');

  // --- § 4.4: шаг Ньютона (правка 1)
  fix('Файл `RefinementSqrt.v` доказывает конкретные значения первых членов', null, {
    note: 'О самом файле RefinementSqrt.v верно: в нём этих двух теорем нет. Обе доказаны в ' + SP + ' (newton_strictly_improves, newton_quality_bound) — страница говорит это следующей фразой (шаг 4, 14.11).' });
  const C1 = 'Обе доказаны отдельно — в файле `Sqrt2Processes.v`: каждый шаг строго точнее предыдущего (`newton_strictly_improves`), а квадратичная погрешность на шаге $n$ не превосходит $1/2^n$ (`newton_quality_bound`), так что процесс достигает любой точности (§ 4.5).';
  add({ theorem: 'newton_strictly_improves', file: SP, claim: C1, note: N_NSI });
  add({ theorem: 'newton_quality_bound', file: SP, claim: C1, note: N_NQB + ' Достижение любой точности — newton_gives_pos_sqrt2.' });

  // --- § 4.4: статус предиката (правка 2, место 4.1)
  fix('Стоит сразу сказать и о статусе этого предиката в репозитории', 'sqrt2_process', {
    theorem: 'gives_sqrt2', file: SP,
    claim: 'Стоит сразу сказать и о статусе этого предиката в репозитории (файл `Sqrt2Processes.v`). В записанном виде он назван там `gives_sqrt2`.',
    note: DONE + ' (формализацией): было «определение sqrt2_process есть естественная формализация» при том, что предиката в src не было, а имя носил ньютонов процесс. ' + N_GIVES });
  const C2a = 'К двум условиям при формализации добавлено третье — неотрицательность членов $R$ (предикат `gives_pos_sqrt2`): без него тому же условию отвечал бы и процесс $-R$ (`gives_sqrt2_opp`).';
  add({ theorem: 'gives_pos_sqrt2', file: SP, claim: C2a, note: N_POS });
  add({ theorem: 'gives_sqrt2_opp', file: SP, claim: C2a, note: N_OPP });
  const C2b = 'С ним условие Коши следует из сходимости квадрата (`pos_sqrt2_Cauchy`), а ньютонов процесс, процесс цепной дроби и процесс деления отрезка пополам предикату отвечают (`newton_gives_pos_sqrt2`, `cf_gives_pos_sqrt2`, `sqrt2_bisect_gives_pos_sqrt2`).';
  add({ theorem: 'pos_sqrt2_Cauchy', file: SP, claim: C2b, note: N_CAU });
  add({ theorem: 'newton_gives_pos_sqrt2', file: SP, claim: C2b, note: 'newton_gives_pos_sqrt2 : gives_pos_sqrt2 sqrt2_newton (:396). ' + CL + '.' });
  add({ theorem: 'cf_gives_pos_sqrt2', file: SP, claim: C2b, note: 'cf_gives_pos_sqrt2 : gives_pos_sqrt2 sqrt2_cf (:300). ' + CL + '.' });
  add({ theorem: 'sqrt2_bisect_gives_pos_sqrt2', file: SP, claim: C2b, note: 'sqrt2_bisect_gives_pos_sqrt2 : gives_pos_sqrt2 sqrt2_bisect (:506). ' + CL + '.' });
  add({ theorem: 'sqrt2_process', file: 'src/stdlib/qphysics/QPhysicsProcesses.v',
    claim: 'Имя `sqrt2_process` в репозитории носит другое — сам ньютонов процесс (файл `QPhysicsProcesses.v`).',
    note: 'Fixpoint sqrt2_process (K : nat) : Q (QPhysicsProcesses.v:47) — функция nat -> Q, не предикат; repo_sqrt2_process_is_newton : forall K, QPhysicsProcesses.sqrt2_process K = sqrt2_newton K (' + SP + ':609). ' + CL + '.' });

  // --- § 4.5: сравнимость качеств (правка 3)
  add({ theorem: 'quality_comparable', file: SP,
    claim: 'оно следует из разрешимости порядка рациональных чисел и записано отдельно (`quality_comparable`, файл `Sqrt2Processes.v`).',
    note: 'quality_comparable : forall K, sqrt2_quality (sqrt2_newton K) <= sqrt2_quality (sqrt2_cf K) ' + BS + '/ sqrt2_quality (sqrt2_cf K) < sqrt2_quality (sqrt2_newton K) (:84). ' + CL + '.' });

  // --- § 4.5: класс один (правка 4); третий процесс и попарная эквивалентность (правка 5)
  add({ theorem: 'pos_sqrt2_unique', file: SP,
    claim: 'При условии неотрицательности членов класс этот один: любые два таких процесса эквивалентны (`pos_sqrt2_unique`, файл `Sqrt2Processes.v`).',
    note: N_UNI });
  const C5 = 'В файле `Sqrt2Processes.v` к ним добавлен третий — процесс деления отрезка пополам (`sqrt2_bisect`), — и доказано, что все три дают ' + SQ + ' и попарно эквивалентны (`newton_cf_equiv`, `newton_bisect_equiv`).';
  add({ theorem: 'sqrt2_bisect', file: SP, claim: C5, note: N_BIS });
  add({ theorem: 'newton_cf_equiv', file: SP, claim: C5, note: 'newton_cf_equiv : PC.process_equiv sqrt2_newton sqrt2_cf (:538). ' + CL + '.' });
  add({ theorem: 'newton_bisect_equiv', file: SP, claim: C5, note: 'newton_bisect_equiv : PC.process_equiv sqrt2_newton sqrt2_bisect (:541). ' + CL + '.' });
  add({ theorem: 'cf_bisect_equiv', file: SP, claim: C5,
    note: 'Третья пара (страница называет две теоремы): cf_bisect_equiv : PC.process_equiv sqrt2_cf sqrt2_bisect (:544) — дописана 14.11 при сверке, чтобы «попарно» стояло теоремами полностью. ' + CL + '.' });

  // --- § 4.6: что утверждает shrinking_interval_Cauchy (правка 6, место 4.2)
  fix('`shrinking_interval_Cauchy` — теорему о том, что процесс, удерживаемый', 'shrinking_interval_Cauchy', {
    claim: '`shrinking_interval_Cauchy` — теорему о том, что процесс, у которого взаимные расстояния приближений ограничены убывающей вдвое шириной — как у процесса, удерживаемого во вложенных интервалах, — есть процесс Коши;',
    note: DONE + ': было «процесс, удерживаемый в интервалах с убывающей шириной»; в посылке теоремы — оценка взаимных расстояний. ' + N_SIC + ' (Archimedean_ERR.v:158). Форма с интервалами в посылке — interval_process_Cauchy (' + SP + ':561).' });

  // --- § 4.7: «процесс сжимающихся интервалов, задающий √2, есть процесс Коши» (место 4.3)
  fix('ToS доказывает эту связь теоремой: процесс *сжимающихся интервалов*', 'shrinking_interval_Cauchy', {
    theorem: 'sqrt2_bisect_Cauchy', file: SP,
    note: DONE + ' (формализацией): такого процесса в src не было; теперь он построен. ' + N_BISC });
  fix('Теорема `shrinking_interval_Cauchy` говорит о процессе', 'shrinking_interval_Cauchy', {
    claim: 'Теорема `shrinking_interval_Cauchy` говорит о процессе с оценкой *особого рода*: расстояние между приближениями с номерами $m ' + LE + ' n$ не превосходит ширины $(b - a)/2^m$ — так ведёт себя процесс сжимающихся интервалов, удерживающий приближения во вложенных отрезках убывающей вдвое ширины.',
    note: DONE + ': было «о процессе особого рода — о процессе сжимающихся интервалов»; род процесса в теореме не ограничен, посылка — оценка расстояний. ' + N_SIC + ' (:559). Ньютонов процесс этой посылке отвечает: newton_distance_bound, newton_Cauchy_by_shrinking (' + SP + ').' });
  fix('и процесс сжимающихся интервалов, задающий', 'shrinking_interval_Cauchy', {
    theorem: 'sqrt2_bisect_Cauchy', file: SP,
    note: DONE + ' (формализацией): ' + N_BISC });

  // --- § 4.7: собственные оценки сходимости (правка 8)
  const C8 = 'Для ньютонова же и цепно-дробного процессов утверждение «это процесс Коши» нуждается в собственных оценках сходимости; они доказаны в файле `Sqrt2Processes.v`: для ньютонова процесса $|x_n^2 - 2| ' + LE + ' 1/2^n$ (`newton_quality_bound`), процесс цепной дроби по шагам совпадает с процессом Пелля (`cf_eq_sx`), погрешность которого равна $1/q_n^2$, и оба суть процессы Коши (`newton_Cauchy_SI`, `cf_Cauchy_SI`; § 4.5).[^18]';
  fix('Для ньютонова же и цепно-дробного процессов утверждение', null, {
    theorem: 'newton_quality_bound', file: SP, claim: C8,
    note: DONE + ' (формализацией): было «эти оценки … не доказаны». ' + N_NQB });
  add({ theorem: 'cf_eq_sx', file: SP, claim: C8, note: 'cf_eq_sx : forall k, sqrt2_cf k == sx k (:294) — sx есть процесс Пелля файла Sqrt2Approx.v. ' + CL + '.' });
  add({ theorem: 'sx_abs_eq', file: 'src/Sqrt2Approx.v', claim: C8, note: 'Погрешность процесса Пелля: sx_abs_eq : forall N, Qabs (sx N * sx N - 2) == / inject_Z (qq N * qq N) (Sqrt2Approx.v:143). ' + CL + '.' });
  add({ theorem: 'newton_Cauchy_SI', file: SP, claim: C8, note: 'newton_Cauchy_SI : SI.is_Cauchy sqrt2_newton (:531). ' + CL + '.' });
  add({ theorem: 'cf_Cauchy_SI', file: SP, claim: C8, note: 'cf_Cauchy_SI : SI.is_Cauchy sqrt2_cf (:534). ' + CL + '.' });

  // --- граница Части III (правка 9, место 4.4)
  fix('Часть III установила:', null, {
    theorem: 'pos_sqrt2_Cauchy', file: SP,
    claim: 'Часть III установила: ' + SQ + ' даётся процессом — функциональной системой рациональных приближений (§ 4.4); процессов таких открытый класс (§ 4.5); всякий такой процесс достигает любой точности (§ 4.6) и есть процесс Коши (§ 4.7; теорема `pos_sqrt2_Cauchy`, файл `Sqrt2Processes.v`).',
    note: DONE + ' (формализацией): «всякий такой процесс … есть процесс Коши» — теорема. ' + N_CAU + ' Достижение любой точности входит в сам предикат (sq_to_2). Открытое семейство по-прежнему не формализовано — страница говорит это сама в § 4.5; предъявлены три члена класса.' });

  // --- итог § 4.7 (курсив; правка 10)
  fix('Процесс *сжимающихся интервалов*, задающий', 'shrinking_interval_Cauchy', {
    theorem: 'sqrt2_bisect_Cauchy', file: SP,
    note: DONE + ' (формализацией): «обладает им доказанно» — ' + N_BISC });
  add({ theorem: 'newton_Cauchy_SI', file: SP,
    claim: 'Для процессов иного типа — ньютонова и цепно-дробного — свойство Коши требует собственных оценок сходимости; они доказаны (§ 4.7).',
    note: 'newton_Cauchy_SI : SI.is_Cauchy sqrt2_newton (:531); cf_Cauchy_SI : SI.is_Cauchy sqrt2_cf (:534); оценки — newton_quality_bound и sx_abs_eq через cf_eq_sx. ' + CL + '.' });

  // --- итог главы
  fix('глава показала, что процесс достигает любой точности', null, {
    theorem: 'newton_gives_pos_sqrt2', file: SP,
    note: DONE + ' (формализацией): для разобранных процессов и то и другое теперь доказано — newton_gives_pos_sqrt2, cf_gives_pos_sqrt2, sqrt2_bisect_gives_pos_sqrt2 (квадрат подходит к двум ближе всякой точности) и pos_sqrt2_Cauchy (процесс Коши). ' + CL + '.' });

  // --- разбор E/R/R (правки 11–13)
  fix('единство процессов взято через *слабое* отношение', 'sqrt2_process', {
    theorem: 'gives_pos_sqrt2', file: SP,
    claim: 'единство процессов взято через *слабое* отношение `process_equiv`, а предикат «даёт ' + SQ + '» записан в файле `Sqrt2Processes.v` (`gives_pos_sqrt2`), и три процесса ему отвечают (§ 4.4–4.5).',
    note: DONE + ' (формализацией): было «предикат sqrt2_process — формализация-цель». ' + N_POS + ' Три процесса: newton_gives_pos_sqrt2, cf_gives_pos_sqrt2, sqrt2_bisect_gives_pos_sqrt2.' });
  fix('| законы $L1$–$L5$ (здесь $L3$ для предела', null, {
    claim: '| законы $L1$–$L5$ (здесь $L3$ для предела; в теоремах этой главы не применяется) | универсальный слой | Rule (универс.) |',
    page_price: 'в теоремах главы L3 не применяется',
    note: DONE + ': слова автора оставлены, добавлен факт о цене. Print Assumptions для всех объявлений Sqrt2Irrational.v, RefinementSqrt.v, Archimedean_ERR.v, ShrinkingIntervals_ERR.v, Sqrt2Processes.v и трёх лемм ProcessCore.v — ' + CL + '.' });
  fix('тогда как теория сжимающихся интервалов § 4.7 опирается', 'shrinking_interval_Cauchy', {
    claim: 'теоремы о сжимающихся интервалах § 4.7 также стоят без $L3$, хотя их файл подключает классическое окружение, — импорт и опора суть разные статусы, смешивать их не следует.',
    page_price: 'без L3',
    note: DONE + ': было «теория сжимающихся интервалов § 4.7 опирается на L3». Print Assumptions shrinking_interval_Cauchy (оба файла), bisect_is_Cauchy, Archimedean_width, sqrt2_bisect_Cauchy — ' + CL + '; файл ShrinkingIntervals_ERR.v подключает ToS_Axioms и Classical_Pred_Type.' });

  // --- сноска 13 (правка 14)
  const C14 = 'Теорема «ньютонов процесс и процесс цепной дроби эквивалентны по `process_equiv`» доказана — `newton_cf_equiv` (файл `Sqrt2Processes.v`); там же общая теорема `pos_sqrt2_unique`: любые два процесса с неотрицательными членами, квадрат которых сходится к двум, эквивалентны.';
  fix('но теорема «ньютонов процесс и процесс цепной дроби эквивалентны', null, {
    theorem: 'newton_cf_equiv', file: SP, claim: C14,
    note: DONE + ' (формализацией): было «в репозитории ещё не доказана». newton_cf_equiv : PC.process_equiv sqrt2_newton sqrt2_cf (:538). ' + CL + '.' });
  add({ theorem: 'pos_sqrt2_unique', file: SP, claim: C14, note: N_UNI });

  // --- сноска 17 (правка 15, место 4.2)
  fix('Теорема `shrinking_interval_Cauchy` файла `ShrinkingIntervals_ERR.v`: если', 'shrinking_interval_Cauchy', {
    claim: 'Теорема `shrinking_interval_Cauchy` файла `ShrinkingIntervals_ERR.v`: если расстояние между приближениями с номерами $m ' + LE + ' n$ не превосходит $(b - a)/2^m$ — как у процесса, держащегося во вложенных интервалах, ширина которых убывает как половинные доли, — то процесс удовлетворяет свойству `is_Cauchy`.',
    note: DONE + ': посылка названа как в теореме — оценка взаимных расстояний. ' + N_SIC + ' (:559). Опора на Archimedean_width подтверждена (:567).' });
  const C15 = 'Для процесса деления отрезка пополам эта оценка проверена теоремой `bisect_is_Cauchy` того же файла, а сам процесс сжимающихся интервалов для ' + SQ + ' — с выбором половины по сравнению квадрата середины с двойкой — построен в файле `Sqrt2Processes.v` (`sqrt2_bisect`, `sqrt2_bisect_Cauchy`).';
  add({ theorem: 'bisect_is_Cauchy', file: SI, claim: C15,
    note: 'bisect_is_Cauchy : forall choose_half s, bis_left s < bis_right s -> is_Cauchy (bisect_process choose_half s) (:845); доказательство применяет shrinking_interval_Cauchy и проверяет оценку расстояний (:851–). ' + CL + '.' });
  add({ theorem: 'sqrt2_bisect', file: SP, claim: C15, note: N_BIS });
  add({ theorem: 'sqrt2_bisect_Cauchy', file: SP, claim: C15, note: N_BISC });

  save();
}
