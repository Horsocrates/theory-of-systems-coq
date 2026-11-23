// Часть VIII, шаг 3, страницы (2026-11-19, слово автора «делай»): 12 правок главы VIII.1 внесены
// (советуемые варианты трёх вопросов: последняя фраза сноски 2 отнесена к § «Где появляется граница»;
// стр. 67–68 оставлены; фраза о шаге h в сноске 8 включена; новая сноска 9).
// Формализация — новые src/process/ProcessPicardLipschitz.v и src/process/ProcessPicardStepContraction.v;
// прежние файлы не менялись.
// Запуск: node patch-p08-step-03-pages.cjs  (затем relocate + merge по part08-ch01). Скрипт повторяем.
// Внимание: L() превращает знак «¤» в обратную косую черту; настоящий знак параграфа пишется прямо.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 19.11 (Часть VIII, шаг 3, слово автора)';
const KEPT = DONE + ' (формализацией; текст фразы не менялся): ';
const CL = 'Closed under the global context';
const PO = 'src/process/ProcessPicardOperator.v';
const GS = 'src/process/ProcessPicardGridSolution.v';
const ER = 'src/process/ProcessEulerRefinement.v';
const PP = 'src/process/ProcessPicard.v';
const PL = 'src/process/ProcessPicardLipschitz.v';
const PS = 'src/process/ProcessPicardStepContraction.v';
const OD = 'src/process/ProcessODE.v';
const FP = 'src/FixedPoint.v';
const SC = 'src/SeriesConvergence.v';
const CR = 'src/CauchyReal.v';
const AP = 'src/analysis/PicardLindelof.v';
const BS = String.fromCharCode(92);
const L = (s) => s.split('¤').join(BS);   // «¤» — обратная косая черта
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

// --- утверждения (номера строк — по src)
const N_CLIP = 'euler_picard_contraction_lip : forall g y0 h L, 0 <= h -> is_lipschitz_auto g L -> L * h < 1 -> is_contraction (euler_picard g y0 h) (y0 - ep_radius g y0 h L) (y0 + ep_radius g y0 h L) (L * h) (ProcessPicardLipschitz.v:128); euler_picard g y0 h y := y0 + g y * h (ProcessPicard.v:115); ep_radius g y0 h L := Qabs (g y0) * h / (1 - L * h) (:83); is_lipschitz_auto g L := 0 < L ' + AND + ' forall y1 y2, Qabs (g y1 - g y2) <= L * Qabs (y1 - y2) (ProcessPicard.v:80). Посылки ограниченности нет. ' + CL + '.';
const N_CAUL = 'euler_picard_cauchy_lip : forall g y0 h L, 0 <= h -> is_lipschitz_auto g L -> L * h < 1 -> is_cauchy (euler_picard_process g y0 h) (ProcessPicardLipschitz.v:142); euler_picard_process g y0 h n = n-я итерация отображения y |-> y0 + g y * h от точки y0 (ProcessPicard.v:192). Для f(t, y) в фиксированный момент t — euler_picard_cauchy_vf (:157). ' + CL + '.';
const N_OLDC = 'euler_picard_contraction : 0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M -> L * h < 1 -> is_contraction (euler_picard g y0 h) (y0 - M * h) (y0 + M * h) (L * h) (ProcessPicard.v:165); is_bounded_auto g M := forall y, Qabs (g y) <= M (:85) — ограниченность на всём Q. ' + CL + '.';
const N_OLDK = 'euler_picard_cauchy : 0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M -> L * h < 1 -> is_cauchy (euler_picard_process g y0 h) (ProcessPicard.v:206). ' + CL + '.';
const N_NB = 'linear_not_bounded_auto : forall a M : Q, ~ a == 0 -> ~ is_bounded_auto (fun y : Q => a * y) M (ProcessPicardLipschitz.v:178) — правая часть a·y при a, отличном от нуля, не ограничена на Q никаким M; для y′ = y — id_not_bounded_auto (:171). Посылки прежней теоремы выполнимы: const_satisfies_both_premises (:188). ' + CL + '.';
const N_FIFF = 'euler_picard_fixed_iff : forall g y0 h p, euler_picard g y0 h p == p <-> p == y0 + h * g p (ProcessPicardLipschitz.v:216). ' + CL + '.';
const N_LIM = 'euler_picard_iterate_limit : forall g y0 h L p, 0 <= h -> is_lipschitz_auto g L -> L * h < 1 -> p == y0 + h * g p -> forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> Qabs (euler_picard_iterate g y0 h n - p) < eps (ProcessPicardLipschitz.v:254); оценка — euler_picard_iterate_to_fixed (:230): Qabs (y_n - p) <= Qpow (L * h) n * Qabs (y0 - p). Рациональное p входит посылкой. ' + CL + '.';
const N_APART = 'scalar_limit_apart_from_euler_stages : (forall eps, 0 < eps -> exists K, forall n, (K <= n)%nat -> Qabs (euler_picard_iterate (fun y : Q => y) 1 (1#2) n - 2) < eps) ' + AND + ' (forall N : nat, (0 < N)%nat -> PicardLindelof.euler_traj PicardLindelof.f_identity 1 (2 * N) N < 7 # 4) (ProcessPicardLipschitz.v:356). Первая часть — linear_scalar_iteration_limit (:294), значения y_n = 2 − (1/2)^n (linear_scalar_iteration_value, :282); вторая — euler_half_below (:330): значение ломаной в узле N сетки из 2N шагов на [0, 1] (момент t = 1/2) равно (1 + 1/(2N))^N (euler_half_closed, :321), его квадрат — стадия лестницы Главы 8.2, меньшая 3 (ProcessExpLadder.exp1_upper), а (7/4)^2 = 49/16 > 3. ' + CL + '.';
const N_ERR = 'ode_is_process_err : forall g y0 h L, is_lipschitz_auto g L -> 0 <= h -> L * h < 1 -> exists sol_proc err_proc : RealProcess, (forall n, sol_proc n == euler_picard_iterate g y0 h n) ' + AND + ' (forall n m, (n <= m)%nat -> Qabs (sol_proc m - sol_proc n) <= err_proc n) ' + AND + ' (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> err_proc n < eps) ' + AND + ' is_Cauchy sol_proc (ProcessPicardLipschitz.v:434). Свидетель процесса-ошибки — ep_err g y0 h L n := Qabs (g y0 * h) * Qpow (L * h) n / (1 - L * h) (:370); оценка — euler_picard_error_process (:383), стремление к нулю — ep_err_vanishes (:406). ' + CL + '.';
const N_OLDP = 'ode_is_process (ProcessODE.v:333): exists sol_proc err_proc, (forall n, sol_proc n == euler_picard_iterate g y0 h n) ' + AND + ' (forall n, 0 <= err_proc n) ' + AND + ' is_Cauchy sol_proc — при посылках is_lipschitz_auto g L, is_bounded_auto g M, 0 <= h, L * h < 1; от процесса-ошибки требуется неотрицательность (ode_is_process_with_zero_err, ProcessPicardLipschitz.v:453: заключение выполняется и при нулевом процессе-ошибке). ' + CL + '.';
const N_NEWT = 'contraction_without_rational_fixed_point : is_contraction newton2 1 2 (1#2) ' + AND + ' is_cauchy (fun n => iterate newton2 1 n) ' + AND + ' (forall p : Q, 1 <= p -> p <= 2 -> ~ newton2 p == p) (ProcessPicardLipschitz.v:516); newton2 x := (1#2) * x + / x (:474). Отсутствие неподвижной точки — newton2_no_rational_fixed_point (:506): из p == p/2 + 1/p следует p * p == 2, что невозможно (Sqrt2Irrational.no_rational_sqrt2). ' + CL + '.';
const N_BFP = 'Definition banach_fixed_point (f : Q -> Q) (a b c x : Q) (Hc : is_contraction f a b c) (Hxa : a <= x) (Hxb : x <= b) : CauchySeq := mkCauchy (fun n => iterate f x n) (iterate_is_cauchy f a b c x Hc Hxa Hxb) (FixedPoint.v:386). Print Assumptions: ' + CL + '.';
const N_IIC = 'iterate_is_cauchy : forall f a b c x, is_contraction f a b c -> a <= x -> x <= b -> is_cauchy (fun n => iterate f x n) (FixedPoint.v:263). ' + CL + '.';
const N_QV = 'Qpow_vanish : forall (r : Q) (eps : Q), 0 < r -> r < 1 -> 0 < eps -> exists N, Qpow r N < eps (SeriesConvergence.v:164); доказательство — через bernoulli_ineq (:126) и свойство Архимеда, без теоремы о монотонной сходимости. ' + CL + '.';
const N_APX = 'approximate_fixed_point : forall f a b c x, is_contraction f a b c -> a <= x -> x <= b -> forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> Qabs (f (iterate f x n) - iterate f x n) < eps (FixedPoint.v:393). ' + CL + '.';
const N_UNQ = 'contraction_unique_fixed : forall f a b c p q, is_contraction f a b c -> a <= p -> p <= b -> a <= q -> q <= b -> f p == p -> f q == q -> p == q (FixedPoint.v:153). ' + CL + '.';
const N_STEP = 'picard_step_contraction : forall (f : VectorField) (L y0 : Q) (y z : Q -> Q) (D t : Q) (N : nat), is_lipschitz f L -> 0 <= t -> 0 <= D -> (forall s, 0 <= s -> s <= t -> Qabs (y s - z s) <= D) -> Qabs (picard_step f y0 y t N - picard_step f y0 z t N) <= (L * t) * D (ProcessPicardStepContraction.v:185); picard_step f y0 y_prev t N := y0 + integral_process (fun s => f s (y_prev s)) 0 t N (ProcessPicard.v:308). Оценка верна при всякой стадии N. ' + CL + '.';
const N_GAP = 'picard_iterate_gap : forall (f : VectorField) (L y0 T C : Q) (N n : nat), is_lipschitz f L -> 0 <= T -> 0 <= C -> (forall t, 0 <= t -> t <= T -> Qabs (picard_iterate f y0 1 t N - picard_iterate f y0 0 t N) <= C) -> forall t, 0 <= t -> t <= T -> Qabs (picard_iterate f y0 (S n) t N - picard_iterate f y0 n t N) <= Qpow (L * T) n * C (ProcessPicardStepContraction.v:220). ' + CL + '.';
const N_UC = 'picard_iterate_uniformly_cauchy : forall (f : VectorField) (L y0 T C : Q) (N : nat), is_lipschitz f L -> 0 <= T -> L * T < 1 -> 0 <= C -> (forall t, 0 <= t -> t <= T -> Qabs (picard_iterate f y0 1 t N - picard_iterate f y0 0 t N) <= C) -> forall eps, 0 < eps -> exists K : nat, forall m n, (K <= m)%nat -> (K <= n)%nat -> forall t, 0 <= t -> t <= T -> Qabs (picard_iterate f y0 m t N - picard_iterate f y0 n t N) < eps (ProcessPicardStepContraction.v:254) — номер K один для всех рациональных t из [0, T]. ' + CL + '.';
const N_SF = 'picard_iterate_modulus_stage_free : forall (f : VectorField) (L y0 T M0 : Q), is_lipschitz f L -> 0 <= T -> L * T < 1 -> 0 <= M0 -> (forall s, 0 <= s -> s <= T -> Qabs (f s y0) <= M0) -> forall eps, 0 < eps -> exists K : nat, forall (N m n : nat), (K <= m)%nat -> (K <= n)%nat -> forall t, 0 <= t -> t <= T -> Qabs (picard_iterate f y0 m t N - picard_iterate f y0 n t N) < eps (ProcessPicardStepContraction.v:306) — номер K стоит до квантора по стадии N; первый зазор оценён числом T·M0 (picard_first_gap_bound, :274). ' + CL + '.';
const N_REACH = 'picard_iter_reaches_fix : forall (N m k : nat), (S N <= m)%nat -> (k <= N)%nat -> picard_iter f h y0 m k = picard_fix N k (ProcessPicardGridSolution.v:224) — начиная с номера N + 1 итерации совпадают с неподвижной точкой во всех узлах. ' + CL + '.';
const N_ISEUL = 'picard_fixed_is_euler : forall N (y : nat -> Q), (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) -> y 0%nat == y0 ' + AND + ' forall k, (k < N)%nat -> y (S k) == y k + h * f (tgrid h k) (y k) (ProcessPicardGridSolution.v:252). ' + CL + '.';
const N_SUPC = 'picard_iter_sup_cauchy : forall (f : Q -> Q -> Q) (L : Q), 0 < L -> (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) -> forall h, 0 <= h -> forall (y0 : Q) (N : nat), L * Tlen h N < 1 -> forall eps, 0 < eps -> exists M : nat, forall m n, (M <= m)%nat -> (M <= n)%nat -> forall k, (k <= N)%nat -> Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k) < eps (ProcessPicardGridSolution.v:611). ' + CL + '.';
const N_DCAU = 'euler_dyadic_is_Cauchy : forall T, 0 <= T -> is_Cauchy (euler_dyadic T) (ProcessEulerRefinement.v:439); посылки раздела Refinement (:168–:175): правая часть g : Q -> Q не зависит от t, липшицева (0 <= L, Qabs (g y1 - g y2) <= L * Qabs (y1 - y2)) и ограничена (Qabs (g y) <= M). ' + CL + '.';
const FOUR = 'Четыре процесса приближений: итерации одного шага (euler_picard_cauchy_lip, ProcessPicardLipschitz.v:142 — при липшицевости и L·h < 1); итерации Пикара на сетке (picard_iter_reaches_fix, ProcessPicardGridSolution.v:224 — для всякой правой части; picard_iter_sup_cauchy, :611 — при L·T < 1); итерации Пикара на функциях Q -> Q (picard_iterate_uniformly_cauchy, ProcessPicardStepContraction.v:254 — при L·T < 1, при каждой стадии N); ломаные Эйлера при удвоении сетки (euler_dyadic_is_Cauchy, ProcessEulerRefinement.v:439 — при автономной правой части, ограниченной и липшицевой). Все — ' + CL + '.';
const NOLIM = 'Теорем о завершённом пределе (числе или функции) в файлах главы нет: во всех теоремах предел либо не упоминается, либо входит посылкой как рациональное число (euler_picard_iterate_limit). Слова об L3 страница относит к тезису § «Где появляется граница» (слово автора).';

// --- цитаты страницы после правок
const C55 = 'В текущем формальном слое переход от геометрического убывания итератов к их *Коши-сходимости* доказан без аксиом; к завершённому пределу формальный слой не переходит вовсе — предел остаётся ролью, и это честно отмечается, а не маскируется под конструкцию.[^2]';
const C60 = '*Первый* — конкретные процессы над ℚ: траектория Эйлера, скалярная итерация Эйлера–Пикара, её сжатие и геометрический зазор итератов — доказаны точно, без аксиом, как и Коши-свойство итераций (сноски 2 и 6).';
const C62 = 'как и Коши-свойство итераций (сноски 2 и 6).';
const C196 = L('Если $f$ липшицева по $y$ с константой $L$, то на достаточно малом шаге $h$ итерация Эйлера–Пикара одного шага — отображение $y ¤mapsto y_0 + h f(y)$ — *сжатие*: расстояние между образами двух приближений строго меньше расстояния между самими приближениями, с коэффициентом $r < 1$.');
const C207 = 'В формальном слое оно доказано для четырёх процессов: для итераций одного шага (их роль-предел — значение одного неявного шага Эйлера, ещё не решение на отрезке); для итераций Пикара на сетке (они приходят к ломаной Эйлера за конечное число шагов); для итераций Пикара на функциях при каждой стадии интеграла-процесса (равномерный процесс Коши на отрезке при $LT<1$); и для самих ломаных Эйлера при удвоении сетки — при автономной правой части, ограниченной и липшицевой.[^9]';
const C232 = 'Доказано конструктивно (0 аксиом) — алгебра сжатия, геометрический зазор итератов (Глава 8.3, `picard_iter_gap`) и сама Коши-сходимость итераций (`picard_iter_sup_cauchy`; лемма о затухании `Qpow_vanish` аксиом не требует — `Print Assumptions`: «closed under the global context»).';
const C236 = 'Завершённого предела формальный слой не строит: он — роль-предел, не актуализируемый как функция-объект.*';
const F1 = 'Скалярное сжатие Эйлера–Пикара и его Коши-свойство — `euler_picard_contraction` и `euler_picard_cauchy` в `ProcessPicard.v` (при правой части, ограниченной на всём ℚ) и `euler_picard_contraction_lip`, `euler_picard_cauchy_lip` в `ProcessPicardLipschitz.v` (при одной липшицевости); банахов слой — `iterate_is_cauchy` в `FixedPoint.v`.';
const F2A = 'Коши-сходимость итератов (`iterate_is_cauchy`) в `FixedPoint.v` и запись итератов как процесса Коши (`banach_fixed_point`) аксиом не требуют: лемма о затухании $c^n$ (`Qpow_vanish`, `SeriesConvergence.v`) доказана через неравенство Бернулли и свойство Архимеда, и `Print Assumptions` для обеих даёт «closed under the global context».';
const F2A2 = 'лемма о затухании $c^n$ (`Qpow_vanish`, `SeriesConvergence.v`) доказана через неравенство Бернулли и свойство Архимеда';
const F2B = 'Так же без аксиом — алгебраическая оценка *сжатия* (`euler_picard_contraction`, `ProcessPicard.v`) и — в расширенном слое Главы 8.3 — *геометрический зазор* итератов и *единственность* решения на сетке (`picard_iter_gap`, `picard_unique` в `ProcessPicardOperator.v`).';
const F2C = 'Стержень главы — различие иного рода: сжатие, зазор и Коши-свойство суть утверждения о рациональных стадиях и строятся без аксиом; перехода к завершённому пределу как объекту в формальном слое нет — по § «Где появляется граница» это уже не конструкция, а постулат L3.';
const F4 = 'Что решение *есть* процесс, а не его предел, зафиксировано в `ode_is_process` (`ProcessODE.v`) и, в усиленном виде, в `ode_is_process_err` (`ProcessPicardLipschitz.v`): пара «процесс-решение / процесс-ошибка», где процесс-решение совпадает с итерацией Эйлера–Пикара одного шага, а процесс-ошибка — во второй записи — оценивает расстояние от стадии до всех следующих и стремится к нулю.';
const F5A = 'Интегральный шаг Пикара `picard_step` определён в `ProcessPicard.v`; интеграл в нём — процесс накопления Части V, взятый на стадии $N$.';
const F5B = L('Сжатие этого оператора на функциях $ℚ¤toℚ$ в равномерной оценке по рациональным точкам отрезка, геометрический зазор его итераций и их равномерное Коши-свойство при $LT<1$ — `picard_step_contraction`, `picard_iterate_gap`, `picard_iterate_uniformly_cauchy` в `ProcessPicardStepContraction.v` (0 аксиом).');
const F5C = L('Полноценная теорема о сжатии оператора Пикара *на пространстве функций* (а не только скалярного шага) — центр Части, Глава 8.3 (`ProcessPicardOperator.v`): там оператор взят в сеточной форме $¤Phi(y)_k = y_0 + h¤sum_{j<k} f(t_j, y_j)$, а пространство функций — значения в узлах сетки.');
const F6A = L('В скалярном слое: `euler_picard_contraction_lip` (`ProcessPicardLipschitz.v`) доказывает, что при липшицевости и $Lh<1$ отображение $y ¤mapsto y_0 + f(y) h$ есть сжатие (`is_contraction`) отрезка $[y_0 - R,¤, y_0 + R]$, $R = ¤lvert f(y_0)¤rvert h/(1 - Lh)$, с коэффициентом $Lh$; прежняя теорема `euler_picard_contraction` (`ProcessPicard.v`) берёт ещё посылку ограниченности правой части на всём ℚ, которой линейная правая часть не удовлетворяет (`linear_not_bounded_auto`).');
const F6B = 'Переход от сжатия к самой *Коши-сходимости* итератов (`euler_picard_cauchy_lip` там же; `euler_picard_cauchy` в `ProcessPicard.v`; `iterate_is_cauchy` в `FixedPoint.v`) идёт через лемму о затухании $c^n$ (`Qpow_vanish`) и тоже аксиом не требует.';
const F6C = 'Иными словами, «приближения образуют процесс Коши» конструктивно целиком — и алгебра сжатия, и предельная оценка, — что и проверяется `Print Assumptions`; за пределами конструкции остаётся только завершённый предел.';
const F6D = 'Роль-предел этой итерации — решение уравнения $p = y_0 + h f(p)$, значение одного неявного шага Эйлера: если такое рациональное $p$ есть, итерации сходятся к нему (`euler_picard_fixed_iff`, `euler_picard_iterate_limit`).';
const F6E = "С пределом стадий ломаной Эйлера он не совпадает: при $y' = y$, $y_0 = 1$, $h = 1/2$ итерация стремится к $2$, а значения ломаных Эйлера в момент $t = 1/2$ (сетки из $2N$ шагов на $[0,1]$, Глава 8.2) все лежат ниже $7/4$ (`scalar_limit_apart_from_euler_stages`).";
const F7A = 'В `FixedPoint.v` `banach_fixed_point` — определение: оно записывает итераты сжатия как процесс Коши (`CauchySeq`) и аксиом не требует.';
const F7B = L('Утверждения «неподвижная точка *существует*» как рационального числа в формальном слое нет, и над ℚ в общем виде его быть не может: сжатие $x ¤mapsto x/2 + 1/x$ отрезка $[1,2]$ не имеет рациональной неподвижной точки ($x^2 = 2$), хотя его итерации образуют процесс Коши (`contraction_without_rational_fixed_point` в `ProcessPicardLipschitz.v`), — предел остаётся ролью.');
const F7C = 'Доказаны приближённая неподвижность итератов (`approximate_fixed_point`) и единственность неподвижной точки (`contraction_unique_fixed`).';
const F7D = 'См. также Главу 8.3: *сжатие на пространстве функций*, *единственность* решения на сетке и *геометрический зазор* итератов (`ProcessPicardOperator.v`), их сходимость и существование решения на сетке (`ProcessPicardGridSolution.v`) доказаны без аксиом; функции-решения на отрезке как завершённого объекта формальный слой не строит.';
const F8A = 'Шапки дают разметку: `ProcessODE.v` — Elements: итераты метода Эйлера, процесс Пикара–Линделёфа; Roles: существование и единственность решения через сходимость процесса; Rules: сжатие Пикара и устойчивость по Гронуоллу.';
const F8B = '`ProcessPicard.v` — Elements: итераты Пикара $y_n(t)$ (рациональные приближения); Roles: процесс Коши, сходящийся к решению; Rules: сжатие при липшицевости.';
const F8C = '`analysis/PicardLindelof.v` — Elements: правая часть $f$, узлы сетки $t_k$, значения траектории $y_k$; Roles: $f$ — поле скорости, $y_k$ — приближение, $h$ — шаг; Rules: шаг Эйлера, сжатие при липшицевости.';
const F8D = 'В таблице главы шаг $h$ отнесён к элементам как рациональное число; шапки называют его по роли.';
const F9A = 'Итерации одного шага — `euler_picard_cauchy_lip` (`ProcessPicardLipschitz.v`).';
const F9B = 'Итерации Пикара на сетке — `picard_iter_reaches_fix`, `picard_fixed_is_euler`, `picard_iter_sup_cauchy` (`ProcessPicardGridSolution.v`, Глава 8.3).';
const F9C = L('Итерации Пикара на функциях $ℚ¤toℚ$ — `picard_iterate_uniformly_cauchy`; номер, с которого итерации $¤varepsilon$-близки, не зависит от стадии интеграла-процесса — `picard_iterate_modulus_stage_free` (`ProcessPicardStepContraction.v`).');
const F9D = 'Ломаные Эйлера при удвоении сетки — `euler_dyadic_is_Cauchy` (`ProcessEulerRefinement.v`, Глава 8.3).';
const F9E = 'Что стадии интеграла-процесса при разных $N$ сближаются и что предел удовлетворяет уравнению, в формальном слое не доказано.';

{
  const { fix, add, save } = open('part08-ch01');

  // ------------------------------------------------------------ вводная часть (места 1.6, 1.3)
  fix('Конкретные методы (Эйлер на сетке — Глава 8.2), полноценная теорема', 'picard_op_contraction', { assumptions: CL,
    note: KEPT + 'сжатие на пространстве функций доказано в двух формах. На сеточных функциях nat -> Q — picard_op_contraction (ProcessPicardOperator.v:102), теорема Главы 8.3. На функциях Q -> Q, для интегрального оператора этой главы: ' + N_STEP + ' Какая форма о чём — страница говорит в сноске 5.' });
  fix('Доказанное ядро — конкретное: траектория Эйлера и (скалярная) итерация', 'euler_picard_contraction', { theorem: 'euler_picard_contraction_lip', file: PL, assumptions: CL,
    note: KEPT + '«при липшицевости и достаточно малом шаге итерация есть сжатие, а значит — процесс Коши» теперь теорема в названных условиях: ' + N_CLIP + ' Свойство Коши: ' + N_CAUL + ' Прежняя теорема с посылкой ограниченности — euler_picard_contraction (ProcessPicard.v:165); сноска 1 называет обе.' });

  // ------------------------------------------------------------ «Чего глава не делает» (место 1.1)
  fix('В текущем формальном слое сам переход от геометрического убывания', 'iterate_is_cauchy', { claim: C55, assumptions: CL, page_price: 'без аксиом',
    note: DONE + ': фраза переписана — слова «наследует закон исключённого третьего (L3)» сняты. ' + N_IIC + ' То же для итерации одного шага (euler_picard_cauchy_lip, ProcessPicardLipschitz.v:142) и итераций на сетке (picard_iter_sup_cauchy, ProcessPicardGridSolution.v:611). ' + NOLIM });
  fix('*Первый* — конкретные процессы над ℚ: траектория Эйлера', 'euler_picard_step_shrink', { claim: C60, assumptions: CL, page_price: 'без аксиом',
    note: 'euler_picard_contraction (ProcessPicard.v:165), euler_picard_contraction_lip (ProcessPicardLipschitz.v:128), euler_picard_step_shrink (ProcessPicard.v:245): |y_{n+1} - y_n| <= (L h)^n * |g(y0) h|; все — ' + CL + '.' });
  fix('Коши-свойство наследует `classic`', 'classic', { theorem: 'euler_picard_cauchy_lip', file: PL, external: undefined, claim: C62, assumptions: CL, page_price: 'без аксиом',
    note: DONE + ': слова «Коши-свойство наследует `classic`» заменены. ' + N_CAUL + ' Так же без допущений — euler_picard_cauchy (ProcessPicard.v:206) и iterate_is_cauchy (FixedPoint.v:263).' });
  fix('Первые два уровня глава ведёт как доказанные', null, { file: PL,
    note: KEPT + 'слово автора — фраза оставлена (вопрос 2 шага 3, вариант 1). Чтение второго уровня «существование как Коши-свойство приближений» теперь записано теоремами. ' + FOUR + ' «Явная отметка там, где предел требует L3» стоит в § «Где появляется граница» — тезис автора; в формальном слое завершённый предел не строится.' });

  // ------------------------------------------------------------ «Решение как роль-предел» (место 1.6)
  fix('Итерация Пикара строит её как процесс', 'picard_step', {
    note: 'Построение определено так: picard_step (ProcessPicard.v:308), picard_iterate (:313), picard_process (:321); интеграл берётся на стадии N процесса integral_process. С 19.11 о picard_iterate доказаны сжатие, зазор и равномерное свойство Коши (ProcessPicardStepContraction.v: picard_step_contraction, :185; picard_iterate_gap, :220; picard_iterate_uniformly_cauchy, :254) — сноска 5.' });

  // ------------------------------------------------------------ «Сжатие порождает сходимость» (места 1.3, 1.4)
  fix('Если $f$ липшицева по $y$ с константой $L$, то на достаточно малом шаге итерация', 'euler_picard_contraction', { theorem: 'euler_picard_contraction_lip', file: PL, claim: C196, assumptions: CL,
    note: DONE + ': итерация названа («одного шага — отображение y |-> y0 + h f(y)»). ' + N_CLIP + ' «Строго меньше» — для различных приближений: |E(x) - E(y)| <= L·h·|x - y| при L·h < 1. Для f(t, y) в фиксированный момент t — euler_picard_cauchy_vf (:157).' });
  fix('Таким образом существование решения переписывается', 'euler_picard_cauchy', { theorem: 'euler_picard_cauchy_lip', file: PL, assumptions: CL,
    note: KEPT + 'к абзацу добавлена фраза о четырёх процессах. ' + FOUR + ' Об итерации одного шага страница теперь говорит прямо: её роль-предел — значение одного неявного шага Эйлера (euler_picard_fixed_iff, ProcessPicardLipschitz.v:216).' });
  add({ theorem: 'euler_picard_iterate_limit', file: PL, assumptions: CL, claim: C207,
    note: DONE + ': новая фраза. «Их роль-предел — значение одного неявного шага Эйлера, ещё не решение на отрезке»: ' + N_FIFF + ' ' + N_LIM + ' Отличие от стадий ломаной — scalar_limit_apart_from_euler_stages (:356), сноска 6.' });
  add({ theorem: 'picard_iter_reaches_fix', file: GS, assumptions: CL, claim: C207,
    note: '«Они приходят к ломаной Эйлера за конечное число шагов»: ' + N_REACH + ' Неподвижная точка есть ломаная: ' + N_ISEUL });
  add({ theorem: 'picard_iterate_uniformly_cauchy', file: PS, assumptions: CL, claim: C207,
    note: '«Равномерный процесс Коши на отрезке при LT < 1, при каждой стадии интеграла-процесса»: ' + N_UC });
  add({ theorem: 'euler_dyadic_is_Cauchy', file: ER, assumptions: CL, claim: C207,
    note: '«Для самих ломаных Эйлера при удвоении сетки — при автономной правой части, ограниченной и липшицевой»: ' + N_DCAU });

  // ------------------------------------------------------------ «Где появляется граница» (места 1.1, 1.4)
  fix('Доказано конечное и процессное: уравнение порождает процесс приближений', 'euler_picard_cauchy', { theorem: 'picard_iter_sup_cauchy', file: GS, assumptions: CL,
    note: KEPT + 'условия, при которых процесс приближений есть процесс Коши, страница называет в разделе «Сжатие порождает сходимость» и в сноске 9. ' + FOUR });
  fix('Доказано конструктивно (0 аксиом) — алгебра сжатия и геометрический зазор', 'picard_iter_gap', { claim: C232, assumptions: CL, page_price: '0 аксиом',
    note: 'picard_iter_gap (ProcessPicardOperator.v:234): на узлах k <= N при первом зазоре <= C выполнено |picard_iter (S n) k - picard_iter n k| <= rpow n * C, rpow n = (L * Tlen)^n. ' + CL + '.' });
  fix('сама Коши-сходимость и завершённый предел в текущем формальном слое', 'Qpow_vanish', { claim: C232, assumptions: CL, page_price: 'аксиом не требует',
    note: DONE + ': курсив переписан — слова «наследуют L3 через `Qpow_vanish`» сняты. ' + N_QV });
  add({ theorem: 'picard_iter_sup_cauchy', file: GS, assumptions: CL, claim: C232, page_price: '0 аксиом',
    note: DONE + ': в курсиве названа теорема о самой Коши-сходимости. ' + N_SUPC });
  add({ theorem: null, file: PL, claim: C236,
    note: DONE + ': новая концовка курсива. Статус честный. ' + NOLIM });

  // ------------------------------------------------------------ сноска 1 (место 1.3)
  fix('Скалярное сжатие Эйлера–Пикара и его Коши-свойство', 'euler_picard_contraction', { claim: F1, assumptions: CL,
    note: DONE + ': названо условие прежней теоремы. ' + N_OLDC });
  fix('Скалярное сжатие Эйлера–Пикара и его Коши-свойство', 'euler_picard_cauchy', { claim: F1, assumptions: CL, note: N_OLDK });
  fix('Скалярное сжатие Эйлера–Пикара и его Коши-свойство', 'iterate_is_cauchy', { claim: F1, assumptions: CL,
    note: N_IIC + ' На неё опираются и euler_picard_cauchy (ProcessPicard.v:206), и euler_picard_cauchy_lip (ProcessPicardLipschitz.v:142).' });
  add({ theorem: 'euler_picard_contraction_lip', file: PL, assumptions: CL, claim: F1, note: DONE + ': новое имя в сноске. ' + N_CLIP });
  add({ theorem: 'euler_picard_cauchy_lip', file: PL, assumptions: CL, claim: F1, note: N_CAUL });

  // ------------------------------------------------------------ сноска 2 (места 1.1, 1.2)
  fix('Банахова теорема о неподвижной точке (`banach_fixed_point`)', 'banach_fixed_point', { claim: F2A, assumptions: CL, page_price: 'аксиом не требует',
    note: DONE + ': «Банахова теорема о неподвижной точке» заменена на «запись итератов как процесса Коши». ' + N_BFP });
  fix('Банахова теорема о неподвижной точке (`banach_fixed_point`)', 'iterate_is_cauchy', { claim: F2A, assumptions: CL, page_price: 'аксиом не требует',
    note: DONE + ': цена названа по компилятору. ' + N_IIC });
  fix('Банахова теорема о неподвижной точке (`banach_fixed_point`)', 'Qpow_vanish', { claim: F2A, assumptions: CL, page_price: 'аксиом не требует',
    note: DONE + ': ' + N_QV });
  fix('Банахова теорема о неподвижной точке (`banach_fixed_point`)', 'classic', { theorem: 'bernoulli_ineq', file: SC, external: undefined, claim: F2A2, assumptions: CL,
    note: DONE + ': имя `classic` со страницы снято. «Доказана через неравенство Бернулли и свойство Архимеда»: bernoulli_ineq (SeriesConvergence.v:126) — неравенство Бернулли над Q; на него и на свойство Архимеда опирается доказательство Qpow_vanish (:164). ' + CL + '.' });
  fix('*Конструктивно (0 аксиом)* здесь другое', 'euler_picard_contraction', { claim: F2B, assumptions: CL, page_price: 'без аксиом', note: N_OLDC });
  fix('*Конструктивно (0 аксиом)* здесь другое', 'picard_iter_gap', { claim: F2B, assumptions: CL, page_price: 'без аксиом',
    note: 'Theorem picard_iter_gap (ProcessPicardOperator.v:234). ' + CL + '.' });
  fix('*Конструктивно (0 аксиом)* здесь другое', 'picard_unique', { claim: F2B, assumptions: CL, page_price: 'без аксиом',
    note: 'Theorem picard_unique (ProcessPicardOperator.v:183): две неподвижные точки picard_op на узлах k <= N совпадают; посылки раздела — липшицевость и L * Tlen < 1. Без посылки на L·T — picard_unique_any_rate (ProcessPicardGridSolution.v:330). ' + CL + '.' });
  fix('Стержень главы — именно это различие', null, { claim: F2C, file: PL,
    note: DONE + ' (вопрос 1 шага 3, вариант 1): различие цены между сжатием, зазором и Коши-свойством снято — все три без аксиом. Слова о постулате L3 отнесены к § «Где появляется граница» (тезис автора). ' + NOLIM });

  // ------------------------------------------------------------ сноска 4 (место 1.5)
  fix('Что решение *есть* процесс, а не его предел', 'ode_is_process', { claim: F4, assumptions: CL, note: DONE + ': названа усиленная запись. ' + N_OLDP });
  add({ theorem: 'ode_is_process_err', file: PL, assumptions: CL, claim: F4,
    note: DONE + ': новое имя в сноске. «Оценивает расстояние от стадии до всех следующих и стремится к нулю»: ' + N_ERR });

  // ------------------------------------------------------------ сноска 5 (место 1.6)
  fix('Интегральный шаг Пикара `picard_step` определён', 'picard_step', { claim: F5A,
    note: 'Definition picard_step f y0 y_prev t N := y0 + integral_process (fun s => f s (y_prev s)) 0 t N (ProcessPicard.v:308); integral_process (process/ProcessIntegral.v:56) — процесс Главы V.5: сумма Римана по левым концам на стадии N.' });
  add({ theorem: 'picard_step_contraction', file: PS, assumptions: CL, claim: F5B, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_STEP });
  add({ theorem: 'picard_iterate_gap', file: PS, assumptions: CL, claim: F5B, page_price: '0 аксиом', note: N_GAP });
  add({ theorem: 'picard_iterate_uniformly_cauchy', file: PS, assumptions: CL, claim: F5B, page_price: '0 аксиом', note: N_UC });
  fix('Полноценная теорема о сжатии оператора Пикара *на пространстве функций*', 'picard_op_contraction', { claim: F5C, assumptions: CL,
    note: DONE + ': названа форма оператора Главы 8.3. picard_op f h y0 y k = y0 + h * sum_{j<k} f(t_j, y_j) (ProcessPicardOperator.v:63); picard_op_contraction (:102) — оценка сжатия на узлах k <= N. О самом picard_step — предыдущая фраза сноски (picard_step_contraction).' });

  // ------------------------------------------------------------ сноска 6 (места 1.1, 1.3, 1.4)
  fix('В скалярном слое: `euler_picard_contraction` (`ProcessPicard.v`) доказывает', 'euler_picard_contraction', { theorem: 'euler_picard_contraction_lip', file: PL, claim: F6A, assumptions: CL, page_price: '0 аксиом',
    note: DONE + ': опора заменена на теорему без посылки ограниченности. ' + N_CLIP + ' R на странице — ep_radius.' });
  fix('В скалярном слое: `euler_picard_contraction` (`ProcessPicard.v`) доказывает', 'is_contraction', { claim: F6A,
    note: 'Definition is_contraction f a b c (FixedPoint.v:47): 0 <= c, c < 1, f переводит [a, b] в себя, |f x - f y| <= c |x - y| на [a, b]. Сжатие определено на отрезке рациональных чисел.' });
  add({ theorem: 'euler_picard_contraction', file: PP, assumptions: CL, claim: F6A, page_price: '0 аксиом', note: N_OLDC });
  add({ theorem: 'linear_not_bounded_auto', file: PL, assumptions: CL, claim: F6A, note: DONE + ': новое имя в сноске. ' + N_NB });
  fix('Переход от сжатия к самой *Коши-сходимости* итератов', 'euler_picard_cauchy', { claim: F6B, assumptions: CL, page_price: 'аксиом не требует',
    note: DONE + ': слова «и потому наследует `classic`» заменены. ' + N_OLDK });
  add({ theorem: 'euler_picard_cauchy_lip', file: PL, assumptions: CL, claim: F6B, page_price: 'аксиом не требует', note: N_CAUL });
  add({ theorem: 'iterate_is_cauchy', file: FP, assumptions: CL, claim: F6B, page_price: 'аксиом не требует', note: N_IIC });
  add({ theorem: 'Qpow_vanish', file: SC, assumptions: CL, claim: F6B, page_price: 'аксиом не требует', note: N_QV });
  fix('Иными словами, «приближения образуют процесс Коши» распадается', null, { claim: F6C, file: PL,
    note: DONE + ': фраза переписана по компилятору. Print Assumptions: euler_picard_contraction_lip, euler_picard_cauchy_lip (ProcessPicardLipschitz.v), euler_picard_contraction, euler_picard_cauchy (ProcessPicard.v), iterate_is_cauchy (FixedPoint.v), Qpow_vanish (SeriesConvergence.v) — все ' + CL + '. ' + NOLIM });
  add({ theorem: 'euler_picard_fixed_iff', file: PL, assumptions: CL, claim: F6D, note: DONE + ': новая фраза. ' + N_FIFF });
  add({ theorem: 'euler_picard_iterate_limit', file: PL, assumptions: CL, claim: F6D, note: N_LIM });
  add({ theorem: 'scalar_limit_apart_from_euler_stages', file: PL, assumptions: CL, claim: F6E, note: DONE + ': новая фраза. ' + N_APART });

  // ------------------------------------------------------------ сноска 7 (места 1.1, 1.2)
  fix('Полная банахова теорема в форме «неподвижная точка *существует*»', 'banach_fixed_point', { claim: F7A, assumptions: CL, page_price: 'аксиом не требует',
    note: DONE + ': `banach_fixed_point` назван определением. ' + N_BFP });
  fix('Полная банахова теорема в форме «неподвижная точка *существует*»', 'classic', { theorem: 'CauchySeq', file: CR, external: undefined, claim: F7A, assumptions: '',
    note: DONE + ': имя `classic` со страницы снято. Record CauchySeq := mkCauchy { cs_seq :> nat -> Q; cs_cauchy : is_cauchy cs_seq } (CauchyReal.v:48) — последовательность рациональных вместе с доказательством свойства Коши (is_cauchy, :43).' });
  add({ theorem: 'contraction_without_rational_fixed_point', file: PL, assumptions: CL, claim: F7B, note: DONE + ': новая фраза. ' + N_NEWT });
  add({ theorem: 'approximate_fixed_point', file: FP, assumptions: CL, claim: F7C, note: DONE + ': новая фраза. ' + N_APX });
  add({ theorem: 'contraction_unique_fixed', file: FP, assumptions: CL, claim: F7C, note: N_UNQ });
  fix('см. также `ProcessPicardOperator.v` (Глава 8.3), где *сжатие на пространстве функций*', null, { claim: F7D, file: GS, page_price: 'без аксиом',
    note: DONE + ': слова об «обёртке, отнесённой к L3-слою» сняты. picard_op_contraction (ProcessPicardOperator.v:102), picard_unique (:183), picard_iter_gap (:234), picard_iter_sup_cauchy (ProcessPicardGridSolution.v:611), picard_fixed_exists (:243) — все ' + CL + '. Определения функции-решения на отрезке в файлах Главы 8.3 нет.' });

  // ------------------------------------------------------------ сноска 8 (место 1.7)
  fix('Шапки дают разметку прямо: `ProcessODE.v` и `ProcessPicard.v`', null, { claim: F8A, file: OD,
    note: DONE + ': пересказ приведён к шапкам. ProcessODE.v (:2–4): «Elements: Euler method iterates, Picard-Lindelöf process; Roles: existence and uniqueness of ODE solutions via process convergence; Rules: Picard contraction + Gronwall stability → ODE well-posedness».' });
  add({ theorem: null, file: PP, claim: F8B,
    note: 'ProcessPicard.v (:2–4): «Elements: Picard iterates y_n(t) (rational approximations); Roles: Cauchy process converging to ODE solution; Rules: Lipschitz contraction via FixedPoint.v».' });
  add({ theorem: null, file: AP, claim: F8C,
    note: 'analysis/PicardLindelof.v (:10–12): «Elements: ODE rhs f, grid points t_k, trajectory values y_k; Roles: f -> VectorField, y_k -> Approximation, h -> StepSize; Rules: Euler recurrence (constitution), Lipschitz contraction (bound)».' });
  add({ theorem: null, file: AP, claim: F8D,
    note: DONE + ' (вопрос 3 шага 3, вариант 1 — фраза включена): в шапке analysis/PicardLindelof.v (:11) шаг стоит в строке Roles («h -> StepSize»); в таблице главы шаг h — среди элементов. Сверка страницы с шапкой, не утверждение о теоремах.' });

  // ------------------------------------------------------------ сноска 9 (место 1.4)
  add({ theorem: 'euler_picard_cauchy_lip', file: PL, assumptions: CL, claim: F9A, page_price: '0 аксиом', note: DONE + ': новая сноска. ' + N_CAUL });
  add({ theorem: 'picard_iter_reaches_fix', file: GS, assumptions: CL, claim: F9B, page_price: '0 аксиом', note: N_REACH });
  add({ theorem: 'picard_fixed_is_euler', file: GS, assumptions: CL, claim: F9B, page_price: '0 аксиом', note: N_ISEUL });
  add({ theorem: 'picard_iter_sup_cauchy', file: GS, assumptions: CL, claim: F9B, page_price: '0 аксиом', note: N_SUPC });
  add({ theorem: 'picard_iterate_uniformly_cauchy', file: PS, assumptions: CL, claim: F9C, page_price: '0 аксиом', note: N_UC });
  add({ theorem: 'picard_iterate_modulus_stage_free', file: PS, assumptions: CL, claim: F9C, page_price: '0 аксиом', note: N_SF });
  add({ theorem: 'euler_dyadic_is_Cauchy', file: ER, assumptions: CL, claim: F9D, page_price: '0 аксиом', note: N_DCAU });
  add({ theorem: null, file: PS, claim: F9E,
    note: DONE + ': новая сноска, горизонт назван. Статус честный: теорем о сближении picard_iterate при разных стадиях N и о том, что предел удовлетворяет уравнению, в ProcessPicardStepContraction.v нет (шапка, раздел «NOT claimed»); is_ode_solution (stdlib/ODE.v:61) не используется.' });

  save();
}
