// Часть VIII, шаг 1, страницы (2026-11-19, слово автора «Делай»): 8 правок главы VIII.2 внесены
// (ошибка 1/N для y' = 2t; лестница (1+1/N)^N — оценки, рост и сближение стадий для всех N; сноски 1, 5, 6, 7, 9, 10).
// Формализация — новые src/process/ProcessExpLadder.v и src/analysis/EulerTrajectoryGeneral.v;
// прежние файлы не менялись.
// Запуск: node patch-p08-step-01-pages.cjs  (затем relocate + merge по part08-ch02). Скрипт повторяем.
// Внимание: строки с настоящим знаком параграфа через L() не пропускать.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 19.11 (Часть VIII, шаг 1, слово автора)';
const KEPT = DONE + ' (формализацией; текст страницы не менялся): ';
const CL = 'Closed under the global context';
const PL = 'src/analysis/PicardLindelof.v';
const ET = 'src/analysis/EulerTrajectoryGeneral.v';
const PE = 'src/process/ProcessExpProcess.v';
const EL = 'src/process/ProcessExpLadder.v';
const BS = String.fromCharCode(92);
const L = (s) => s.split('§').join(BS);   // «§» — обратная косая черта
const AND = '/' + BS;
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

function open(name) {
  const p = path.join(__dirname, name + '.json');
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  const pick = (prefix, th, file) => {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix)
      && (th === undefined || (th === null ? !r.theorem : r.theorem === th))
      && (file === undefined || r.file === file));
    if (hit.length > 1) throw new Error(name + ': не одна запись: ' + prefix + ' / ' + th);
    return hit[0];
  };
  const fix = (prefix, th, fields, file) => { const r = pick(prefix, th, file); if (!r) return; Object.assign(r, { verdict: 'ok' }, fields); n++; };
  const add = (rec) => {
    if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && (r.file || null) === (rec.file || null) && norm(r.claim) === norm(rec.claim))) return;
    j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
  };
  const save = () => {
    const seen = new Set(); const before = j.records.length;
    j.records = j.records.filter((r) => { const k = (r.theorem || '') + '|' + (r.file || '') + '|' + norm(r.claim); if (seen.has(k)) return false; seen.add(k); return true; });
    if (before !== j.records.length) console.log(name + '.json: снято дублей ' + (before - j.records.length));
    fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
    console.log(name + '.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length + ', не «верно» ' + j.records.filter((r) => r.verdict !== 'ok').length);
  };
  return { j, fix, add, save };
}

// --- утверждения новых файлов (номера строк — по src)
const N_CONST = 'euler_traj_const_exact : forall (a y0 : Q) (N k : nat), euler_traj (f_const a) y0 N k == y0 + a * grid N k (EulerTrajectoryGeneral.v:79) — всякая постоянная правая часть a (f_const, PicardLindelof.v:322), всякое начальное значение, всякая сетка, всякий узел; посылок нет. Следствия: euler_traj_linear_exact : euler_traj f_const_one 0 N k == grid N k (:89); euler_traj_linear_end : (0 < N)%nat -> euler_traj f_const_one 0 N N == 1 (:96). ' + CL + '.';
const N_QCL = 'euler_traj_quadratic_closed : forall N k : nat, euler_traj f_two_t 0 N k == grid N k * grid N k - grid N k * (1 / inject_Z (Z.of_nat N)) (EulerTrajectoryGeneral.v:105) — без посылок; euler_quadratic_defect (:116): отставание от t_k² в узле k равно grid N k * (1 / inject_Z (Z.of_nat N)). ' + CL + '.';
const N_QERR = 'euler_quadratic_error_general : forall N : nat, (0 < N)%nat -> 1 - euler_traj f_two_t 0 N N == 1 / inject_Z (Z.of_nat N) (EulerTrajectoryGeneral.v:122). Посылка 0 < N — сетка хотя бы из одного шага. ' + CL + '.';
const N_QUND = 'euler_quadratic_underestimates : forall N : nat, (0 < N)%nat -> euler_traj f_two_t 0 N N < 1 (EulerTrajectoryGeneral.v:129) — значение метода в момент t = 1 строго меньше точного. ' + CL + '.';
const N_QDEC = 'euler_quadratic_error_decreases : forall N : nat, (0 < N)%nat -> 1 - euler_traj f_two_t 0 (S N) (S N) < 1 - euler_traj f_two_t 0 N N (EulerTrajectoryGeneral.v:140) — при переходе от сетки N к сетке N + 1 ошибка строго убывает. ' + CL + '.';
const N_ECL = 'euler_traj_exp_closed : forall (y0 : Q) (N k : nat), euler_traj f_identity y0 N k == y0 * qpow (1 + 1 / inject_Z (Z.of_nat N)) k (EulerTrajectoryGeneral.v:159) — без посылок. ' + CL + '.';
const N_LINK = 'exp1_is_euler_traj : forall N : nat, exp1_process N == euler_traj f_identity 1 (S N) (S N) (EulerTrajectoryGeneral.v:176); euler_traj_is_euler_yeqy : forall (y0 : Q) (N k : nat), euler_traj f_identity y0 N k == euler_yeqy (1 / inject_Z (Z.of_nat N)) y0 k (:169) — рекурсия главы (euler_traj) и локальная рекурсия ProcessExpProcess.v (euler_yeqy, :40) связаны теоремой. ' + CL + '.';
const N_UP = 'exp1_upper : forall N : nat, exp1_process N < 3 (ProcessExpLadder.v:601). Доказательство — через qpow_quad_strict (:318): при 0 < h и (k+1)·h <= 1 верно (1 + h)^(k+1) < 1 + (k+1)·h + ((k+1)·h)²; бином не используется. ' + CL + '.';
const N_INC = 'exp1_increasing : forall N : nat, exp1_process N < exp1_process (S N) (ProcessExpLadder.v:657) — строгий рост на каждой стадии. ' + CL + '.';
const N_MOD = 'exp1_modulus : forall N0 m n : nat, (N0 <= m)%nat -> (N0 <= n)%nat -> Qabs (exp1_process m - exp1_process n) < 3 / inject_Z (Z.of_nat (S N0)) (ProcessExpLadder.v:699). exp1_process N есть стадия разрешения N + 1 (ProcessExpProcess.v:47), поэтому в счёте по разрешениям: при разрешениях не меньше N0 + 1 разность меньше 3/(N0 + 1). ' + CL + '.';
const N_CAU = 'exp1_is_Cauchy : is_Cauchy exp1_process (ProcessExpLadder.v:729), где is_Cauchy R := forall eps, 0 < eps -> exists N, forall m n, (N <= m)%nat -> (N <= n)%nat -> Qabs (R m - R n) < eps (ProcessCore.v:68). Номер стадии предъявлен явно — из exp1_modulus (:699) и ladder_archimedean (:86). ' + CL + '.';
const N_LAD = 'exp1_ladder : forall N : nat, 2 <= exp1_process N ' + AND + ' exp1_process N < exp1_process (S N) ' + AND + ' exp1_process (S N) < 3 (ProcessExpLadder.v:669). ' + CL + '.';
const N_SAND = 'euler_traj_exp_sandwich_all : forall N : nat, 2 <= euler_traj f_identity 1 (S N) (S N) ' + AND + ' euler_traj f_identity 1 (S N) (S N) < 3 (EulerTrajectoryGeneral.v:191) — на траектории главы, при всяком разрешении N + 1. ' + CL + '.';
const N_TINC = 'euler_traj_exp_increasing : forall N : nat, euler_traj f_identity 1 (S N) (S N) < euler_traj f_identity 1 (S (S N)) (S (S N)) (EulerTrajectoryGeneral.v:200). ' + CL + '.';
const N_TMOD = 'euler_exp_ladder_modulus : forall N0 m n : nat, (N0 <= m)%nat -> (N0 <= n)%nat -> Qabs (euler_exp_ladder m - euler_exp_ladder n) < 3 / inject_Z (Z.of_nat (S N0)) (EulerTrajectoryGeneral.v:210), где euler_exp_ladder N := euler_traj f_identity 1 (S N) (S N) (:207); euler_exp_ladder_is_Cauchy : is_Cauchy euler_exp_ladder (:217). ' + CL + '.';

// --- цитаты страницы после правок
const C142 = 'Метод недооценивает решение (выпуклая кривая обгоняет свои касательные), и мера этого отставания на каждой конкретной сетке вычислена точно: в момент $t = 1$ ошибка равна шагу сетки, $1/N$.';
const C144 = 'Уменьшение ошибки — это *измельчение сетки*, рост $N$: следующее направление процесса, а не достроенный предел.';
const C179 = 'Каждая стадия конечна и предъявима; ни одна не равна $e$; и сходимость — это свойство процесса (монотонный рост, ограниченность сверху), а не достроенный объект на его конце.';
const C183 = "тамошняя последовательность $(1+1/(N{+}1))^{N+1}$ — та же лестница рациональных стадий, и доказано, что она *есть* траектория Эйлера уравнения $y' = y$ при $t = 1$, ограничена снизу двойкой (по неравенству Бернулли) и сверху тройкой и растёт на каждой стадии — всё это *для всех* $N$;";
const C186 = 'доказано и то, что стадии сближаются: при разрешениях не меньше $N_0$ любые две стадии $(1+1/N)^N$ различаются меньше чем на $3/N_0$.[^9]';
const C188 = 'Честная граница данного слоя — завершённый предел: явное число $e$ как завершённая трансцендентность — роль-предел.';
const C189 = L('Доказано конкретное: рациональные стадии, оценки $2 §le (1+1/N)^N < 3$, рост и сближение стадий для всех $N$; завершённое $e$ не строится.');
const F1A = 'Опорные файлы (Rocq-репозиторий ToS). `analysis/PicardLindelof.v`: `grid`, `euler_step`, `euler_traj` и теоремы о конкретных траекториях (`euler_traj_linear_4`, `euler_quadratic_error`, `euler_traj_exp_4` и др.) — точная рациональная арифметика (`vm_compute`, `field` или `ring`).';
const F1B = '`analysis/EulerTrajectoryGeneral.v`: те же три траектории в общем виде — на всякой сетке и во всяком узле (`euler_traj_const_exact`, `euler_traj_quadratic_closed`, `euler_traj_exp_closed`).';
const F1C = 'Для экспоненты как процесса — `ProcessExpProcess.v` и `ProcessExpLadder.v` (Глава 8.5): оценки, рост и сближение стадий для всех $N$. Все — 0 аксиом (проверено `Print Assumptions`).';
const F5B = L('В общем виде — `euler_traj_const_exact` в `EulerTrajectoryGeneral.v`: при всякой постоянной правой части $a$, всяком начальном значении, на всякой сетке и во всяком узле $y_k = y_0 + a§,t_k$.');
const F6B = 'В общем виде — в `EulerTrajectoryGeneral.v`: `euler_traj_quadratic_closed` ($y_k = t_k^2 - t_k h$ на всякой сетке, $h = 1/N$), `euler_quadratic_error_general` (в момент $t = 1$ ошибка равна $1/N$), `euler_quadratic_underestimates` (ошибка положительна) и `euler_quadratic_error_decreases` (с ростом $N$ она убывает).';
const F7B = L('Замкнутый вид всей траектории — `euler_traj_exp_closed` в `EulerTrajectoryGeneral.v`: $y_k = y_0§,(1+1/N)^k$ на всякой сетке.');
const F9A = L("`exp1_is_euler` (тождество «$e$-процесс${}={}$траектория Эйлера для $y'=y$ при $t=1$»), `exp1_lower` ($e$-процесс${}§ge 2$ *для всех* $N$, через Бернулли) и стадии $2, 9/4, 64/27$ (`exp1_0`, `_1`, `_2`) — в `ProcessExpProcess.v` (Глава 8.5).");
const F9B = '`exp1_upper` ($e$-процесс${}< 3$ *для всех* $N$), `exp1_increasing` (рост *для всех* $N$), `exp1_modulus` (за номером $N_0$ любые две стадии различаются меньше чем на $3/(N_0+1)$) и `exp1_is_Cauchy` (лестница — процесс Коши) — в `ProcessExpLadder.v`.';
const F9C = 'Что та же лестница есть `euler_traj` этой главы при $k = N$ — `exp1_is_euler_traj` в `EulerTrajectoryGeneral.v`;';
const F9D = 'там же оценки, рост и сближение стадий записаны для самой траектории (`euler_traj_exp_sandwich_all`, `euler_traj_exp_increasing`, `euler_exp_ladder_modulus`). Все — 0 аксиом (проверено `Print Assumptions`).';
const F10A = 'Шапка `PicardLindelof.v` даёт разметку прямо: Elements — правая часть $f$, узлы сетки $t_k$, значения траектории $y_k$; Roles — $f$ как векторное поле, $y_k$ как приближение, $h$ как размер шага; Rules — рекуррентность Эйлера $y_{k+1} = y_k + h f(t_k,y_k)$ и липшицево сжатие как оценка.';
const F10B = 'Траектория как процесс (`nat -> Q`) названа там же, в строке о связи с P4.';

{
  const { fix, add, save } = open('part08-ch02');

  // ------------------------------------------------------------ «Что эта глава утверждает — и что нет» (стр. 27–35)
  fix('её значения на эталонных уравнениях вычислены точно', 'euler_traj_linear_4', { theorem: 'euler_traj_const_exact', file: ET, assumptions: CL,
    note: KEPT + 'было доказано совпадение с решением в трёх узлах одной сетки (euler_traj_linear_1, _2, _4, PicardLindelof.v:142–:154) и в одном узле для y′ = 3 (:324). Теперь: ' + N_CONST });
  fix('для квадратичного даёт явную рациональную ошибку', 'euler_quadratic_error', {
    note: 'euler_quadratic_error : 1 - euler_traj f_two_t 0 4 4 == 1 # 4 (PicardLindelof.v:172) — сетка N = 4, момент t = 1. С 19.11 то же на всякой сетке: ' + N_QERR });
  fix('для экспоненциального — последовательность $(1+1/N)^N$ рациональных приближений', 'euler_traj_exp_converges', { theorem: 'euler_traj_exp_sandwich_all', file: ET, assumptions: CL,
    note: KEPT + 'сверху тройкой были оценены четыре стадии (N = 4 — PicardLindelof.v:120, :282; N = 1, 2, 3 — exp1_below3, ProcessExpProcess.v:152). Теперь: ' + N_SAND + ' Для e-процесса главы 8.5 — ' + N_UP });
  fix('Чего глава *не* делает', null, {
    note: 'Статус честный и после шага 1: в четырёх опорных файлах главы нет ни определения предела как объекта, ни теоремы о сходимости траектории Эйлера к решению общего уравнения. Добавлено свойство процесса: лестница (1 + 1/N)^N — процесс Коши с явным модулем (exp1_is_Cauchy, ProcessExpLadder.v:729; euler_exp_ladder_is_Cauchy, EulerTrajectoryGeneral.v:217); шапки обоих новых файлов называют несделанное в разделе «NOT claimed». Лемма с именем euler_traj_exp_converges (PicardLindelof.v:120) по утверждению есть сравнение чисел 625 # 256 < 3.' });

  // ------------------------------------------------------------ линейное уравнение (стр. 129–133)
  fix('Причина точности проста', 'euler_traj_linear_4', { theorem: 'euler_traj_const_exact', file: ET, assumptions: CL,
    note: KEPT + 'общие слова («для уравнений без кривизны») опирались на три узла сетки N = 4 для y′ = 1 и один узел для y′ = 3. Теперь: ' + N_CONST + ' «Без кривизны» страница сама читает как «правая часть постоянна» (сноска 5).' });

  // ------------------------------------------------------------ квадратичное уравнение (стр. 142–146)
  fix('Метод недооценивает решение', 'euler_quadratic_error', { claim: C142, theorem: 'euler_quadratic_error_general', file: ET, assumptions: CL,
    note: DONE + ': к словам «на каждой конкретной сетке вычислена точно» добавлено само значение — в момент t = 1 ошибка равна шагу сетки. Было: одна сетка, N = 4 (euler_quadratic_error, PicardLindelof.v:172). Теперь: ' + N_QERR + ' В произвольном узле — ' + N_QCL });
  add({ theorem: 'euler_quadratic_underestimates', file: ET, assumptions: CL, claim: C142, note: '«Метод недооценивает решение»: ' + N_QUND });
  add({ theorem: 'euler_quadratic_error_decreases', file: ET, assumptions: CL, claim: C144,
    note: 'Убывание ошибки с ростом N — теорема: ' + N_QDEC + ' Предел N → ∞ не строится — как и сказано на странице.' });

  // ------------------------------------------------------------ экспонента (стр. 158–191)
  fix('так что после $N$ шагов размера', 'euler_yeqy_closed', { theorem: 'euler_traj_exp_closed', file: ET, assumptions: CL,
    note: KEPT + 'замкнутый вид был доказан для локальной рекурсии euler_yeqy (ProcessExpProcess.v:71), для euler_traj главы — только при N = 1, 2, 4 (PicardLindelof.v:87, :98, :109). Теперь: ' + N_ECL + ' При y0 = 1 и k = N это (1 + 1/N)^N. Связь двух рекурсий: ' + N_LINK });
  fix('Последовательность $(1+1/N)^N$ — это *не* завершённое число', null, {
    note: '2, 9/4, 625/256 — euler_traj_exp_1, _2, _4 (PicardLindelof.v:87, :98, :109); 64/27 — exp1_2 (ProcessExpProcess.v:64), стадия разрешения 3. Для euler_traj при N = 3 отдельной леммы нет; замкнутый вид на всякой сетке — euler_traj_exp_closed (EulerTrajectoryGeneral.v:159), связь с exp1_process — exp1_is_euler_traj (:176).' });
  add({ theorem: 'exp1_ladder', file: EL, assumptions: CL, claim: C179,
    note: KEPT + 'монотонный рост и ограниченность сверху названы свойствами процесса; до 19.11 они были проверены на отдельных стадиях. Теперь: ' + N_LAD + ' Свойство Коши — ' + N_CAU + ' «Ни одна не равна e» — теоремы нет и в этом слое быть не может: e как объект не строится; из строгого роста следует, что никакие две стадии не равны между собой.' });
  fix('тамошняя последовательность', 'exp1_is_euler', { claim: C183,
    note: DONE + ': фраза переписана. Lemma exp1_is_euler : forall N, exp1_process N == euler_yeqy (1 / inject_Z (Z.of_nat (S N))) 1 (S N) (ProcessExpProcess.v:81); euler_yeqy (:40) — локальная рекурсия этого файла. Что та же лестница есть euler_traj главы: ' + N_LINK });
  fix('тамошняя последовательность', 'exp1_lower', { claim: C183,
    note: 'Lemma exp1_lower : forall N, 2 <= exp1_process N (ProcessExpProcess.v:129); доказательство — через bernoulli_nonneg (:91): 0 <= x -> 1 + n·x <= qpow (1 + x) n.' });
  fix('тамошняя последовательность', 'exp1_climb', { claim: C183, theorem: 'exp1_increasing', file: EL, assumptions: CL,
    note: DONE + ': было «рост проверен на конкретных стадиях» (exp1_climb, ProcessExpProcess.v:149 — две пары соседних стадий). Теперь: ' + N_INC });
  add({ theorem: 'exp1_upper', file: EL, assumptions: CL, claim: C183, note: DONE + ': слова «и сверху тройкой… для всех N» имеют опору: ' + N_UP });
  add({ theorem: 'exp1_is_euler_traj', file: ET, assumptions: CL, claim: C183, note: '«Она есть траектория Эйлера» — для траектории самой главы: ' + N_LINK });
  add({ theorem: 'exp1_modulus', file: EL, assumptions: CL, claim: C186,
    note: DONE + ': новое утверждение страницы (сближение стадий). ' + N_MOD + ' Страница считает по разрешениям: «при разрешениях не меньше N₀… меньше чем на 3/N₀» — это exp1_modulus при N0 := N₀ − 1 (N₀ >= 1). На траектории главы — ' + N_TMOD });
  fix('Полная монотонность для всех $N$', null, { claim: C188, file: EL,
    note: DONE + ': прежняя фраза называла границей рост и оценку < 3 для всех N; оба утверждения доказаны (exp1_increasing, exp1_upper, ProcessExpLadder.v:657, :601). Границей названо то, что ею осталось: в ProcessExpLadder.v и EulerTrajectoryGeneral.v утверждений о пределе как объекте нет — доказаны свойства стадий и свойство Коши (утверждение о процессе с явным номером стадии); шапки обоих файлов называют несделанное в разделе «NOT claimed» (число e как завершённый объект, его иррациональность).' });
  fix('Доказано конкретное: отдельные рациональные стадии', 'exp1_below3', { claim: C189, theorem: 'exp1_ladder', file: EL, assumptions: CL,
    note: DONE + ': перечень приведён к доказанному. Стадии: exp1_0, exp1_1, exp1_2 (ProcessExpProcess.v:58–:64). Оценки и рост для всех N: ' + N_LAD + ' Сближение стадий: exp1_modulus (:699), exp1_is_Cauchy (:729).' });
  fix('Сходимость $(1+1/N)^N', null, {
    note: 'Описание двух режимов; форма утверждений ему отвечает. Режим «рост N при k = N» с 19.11 записан определением euler_exp_ladder N := euler_traj f_identity 1 (S N) (S N) (EulerTrajectoryGeneral.v:207) и теоремами о нём (оценки, рост, свойство Коши — :191, :200, :210, :217); режим «рост k при фиксированном N» — euler_traj_linear_exact (:89). Предел как объект не строится, и страница его не заявляет (стр. 33–37).' });

  // ------------------------------------------------------------ сноска 1
  fix('Опорный файл — `analysis/PicardLindelof.v`', null, { claim: F1A,
    note: DONE + ': сноска переписана — названы четыре опорных файла. PicardLindelof.v: все шесть объявлений есть — grid (:28), euler_step (:33), euler_traj (:36), euler_traj_linear_4 (:154), euler_quadratic_error (:172), euler_traj_exp_4 (:109); в файле 23 Qed (шапка: 23).' });
  fix('Все — точная рациональная арифметика', 'vm_compute', { claim: F1A, page_price: '',
    note: 'vm_compute закрывает три леммы о стадиях экспоненты (PicardLindelof.v:87, :98, :109). Перечень тактик с 19.11 полон: добавлена field.' });
  fix('Все — точная рациональная арифметика', 'ring', { claim: F1A, page_price: '',
    note: 'ring закрывает euler_step_concrete (PicardLindelof.v:68), euler_step_additive, euler_step_scaling, grid_0; сравнения чисел — lia после развёртывания Qlt; euler_traj_0 — lra.' });
  add({ theorem: 'field', external: true, assumptions: 'не применимо (тактика)', claim: F1A,
    note: DONE + ': тактика field добавлена в перечень — ею закрыты названные в сноске euler_traj_linear_4 и euler_quadratic_error (PicardLindelof.v:157, :175). Это тактика Rocq; одноимённое определение field в src/foundation/KnowledgeDeterminacy.v:106 к главе отношения не имеет.' });
  add({ theorem: null, file: ET, claim: F1B,
    note: DONE + ': новый файл назван. src/analysis/EulerTrajectoryGeneral.v — 18 Qed, одно определение (euler_exp_ladder); строк Axiom, Parameter, Admitted нет. Три названные теоремы: euler_traj_const_exact (:79), euler_traj_quadratic_closed (:105), euler_traj_exp_closed (:159) — каждая с кванторами по сетке N и узлу k, без посылок.' });
  add({ theorem: null, file: EL, page_price: '0 аксиом', claim: F1C,
    assumptions: 'все объявления четырёх файлов (PicardLindelof.v — 23 утверждения, EulerTrajectoryGeneral.v — 19 объявлений, ProcessExpProcess.v — 12 утверждений, ProcessExpLadder.v — 44 объявления): ' + CL,
    note: DONE + ': убрано слово «батч C», названа проверка. src/process/ProcessExpLadder.v — 44 Qed; строк Axiom, Parameter, Admitted нет; оценки — exp1_upper (:601) и exp1_lower (ProcessExpProcess.v:129), рост — exp1_increasing (:657), сближение стадий — exp1_modulus (:699). Print Assumptions всех объявлений четырёх файлов — ' + CL + ' (новые файлы — _p08step1/VerifyA.v, VerifyB.v). Оговорка: глава 8.5 сейчас называет только ProcessExpProcess.v; ProcessExpLadder.v она назовёт на шаге 5 — до того ссылка «(Глава 8.5)» для второго файла есть ссылка на тему главы.' });

  // ------------------------------------------------------------ сноски 5, 6, 7
  add({ theorem: 'euler_traj_const_exact', file: ET, assumptions: CL, claim: F5B, note: DONE + ': добавлено имя общей теоремы. ' + N_CONST });
  add({ theorem: 'euler_traj_quadratic_closed', file: ET, assumptions: CL, claim: F6B, note: DONE + ': добавлены имена общих теорем. ' + N_QCL + ' На странице h = 1/N — в утверждении 1 / inject_Z (Z.of_nat N).' });
  add({ theorem: 'euler_quadratic_error_general', file: ET, assumptions: CL, claim: F6B, note: N_QERR });
  add({ theorem: 'euler_quadratic_underestimates', file: ET, assumptions: CL, claim: F6B, note: '«Ошибка положительна»: ' + N_QUND });
  add({ theorem: 'euler_quadratic_error_decreases', file: ET, assumptions: CL, claim: F6B, note: N_QDEC });
  add({ theorem: 'euler_traj_exp_closed', file: ET, assumptions: CL, claim: F7B, note: DONE + ': добавлен замкнутый вид траектории главы. ' + N_ECL });

  // ------------------------------------------------------------ сноска 9
  fix('`exp1_is_euler` (тождество', 'exp1_0', { claim: F9A,
    note: DONE + ': сноска переписана. exp1_process 0 == 2 (ProcessExpProcess.v:58), exp1_process 1 == 9 # 4 (:61), exp1_process 2 == 64 # 27 (:64); exp1_is_euler (:81) и exp1_lower (:129) — с квантором forall N. Упоминание exp1_climb снято: рост теперь доказан для всех N (exp1_increasing).' });
  fix('`exp1_is_euler` (тождество', '_1', { claim: F9A,
    note: 'Сокращённая запись имени exp1_1 (ProcessExpProcess.v:61): exp1_process 1 == 9 # 4, ' + CL + '; отдельного имени _1 нет.' });
  add({ theorem: 'exp1_upper', file: EL, assumptions: CL, claim: F9B, note: N_UP });
  add({ theorem: 'exp1_increasing', file: EL, assumptions: CL, claim: F9B, note: N_INC });
  add({ theorem: 'exp1_modulus', file: EL, assumptions: CL, claim: F9B, note: N_MOD + ' Сноска считает по номерам стадий процесса («за номером N₀… 3/(N₀+1)») — дословно по утверждению.' });
  add({ theorem: 'exp1_is_Cauchy', file: EL, assumptions: CL, claim: F9B, note: N_CAU });
  add({ theorem: 'exp1_is_euler_traj', file: ET, assumptions: CL, claim: F9C, note: N_LINK + ' «При k = N» — в утверждении оба аргумента равны S N.' });
  add({ theorem: 'euler_traj_exp_sandwich_all', file: ET, assumptions: CL, claim: F9D, note: N_SAND });
  add({ theorem: 'euler_traj_exp_increasing', file: ET, assumptions: CL, claim: F9D, note: N_TINC });
  add({ theorem: 'euler_exp_ladder_modulus', file: ET, assumptions: CL, claim: F9D, note: N_TMOD });
  fix('Все в `ProcessExpProcess.v` (Глава 8.5, батч C)', null, { claim: F9D, file: EL, page_price: '0 аксиом',
    assumptions: 'все объявления трёх файлов (ProcessExpProcess.v — 12 утверждений, ProcessExpLadder.v — 44 объявления, EulerTrajectoryGeneral.v — 19 объявлений): ' + CL,
    note: DONE + ': убрано слово «батч C»; цена относится к трём названным в сноске файлам. Print Assumptions: 12 утверждений ProcessExpProcess.v (команды для exp1_is_euler и exp1_lower стоят в конце самого файла, :166–:167), 44 объявления ProcessExpLadder.v и 19 объявлений EulerTrajectoryGeneral.v (_p08step1/VerifyA.v, VerifyB.v) — ' + CL + '.' });

  // ------------------------------------------------------------ сноска 10
  fix('Шапка `PicardLindelof.v` даёт разметку прямо', null, { claim: F10A,
    note: DONE + ': роли и правила приведены к записанным в шапке (PicardLindelof.v:10–:12): «Elements: ODE rhs f, grid points t_k, trajectory values y_k»; «Roles: f -> VectorField, y_k -> Approximation, h -> StepSize»; «Rules: Euler recurrence (constitution), Lipschitz contraction (bound)». Формула шага — в строке :6 шапки: y_{k+1} = y_k + h*f(t_k,y_k).' });
  add({ theorem: null, file: PL, claim: F10B,
    note: DONE + ': «траектория как процесс» отнесена к своей строке шапки (PicardLindelof.v:14–:15): «P4 connection: Euler trajectory IS a process (nat -> Q), convergence of (1+1/N)^N to e is a process limit».' });

  save();
}
