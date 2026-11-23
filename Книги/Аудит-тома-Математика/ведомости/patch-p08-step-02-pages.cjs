// Часть VIII, шаг 2, страницы (2026-11-19, слово автора «Делай»): 17 правок главы VIII.3 внесены
// (советуемые варианты всех трёх вопросов: слово «L3-слой» за функцией-решением снято; абзац и курсив о
// локальности переписаны; неподвижная точка на сетке названа актуальной; сноски 1, 2, 3, 6, 7, 8; новые 10–12).
// Формализация — новые src/process/ProcessPicardGridSolution.v и src/process/ProcessEulerRefinement.v;
// прежние файлы не менялись.
// Запуск: node patch-p08-step-02-pages.cjs  (затем relocate + merge по part08-ch03). Скрипт повторяем.
// Внимание: строки с настоящим знаком параграфа через L() не пропускать.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 19.11 (Часть VIII, шаг 2, слово автора)';
const KEPT = DONE + ' (формализацией; текст фразы не менялся): ';
const CL = 'Closed under the global context';
const PO = 'src/process/ProcessPicardOperator.v';
const GS = 'src/process/ProcessPicardGridSolution.v';
const ER = 'src/process/ProcessEulerRefinement.v';
const PP = 'src/process/ProcessPicard.v';
const SC = 'src/SeriesConvergence.v';
const EL = 'src/process/ProcessExpLadder.v';
const PL = 'src/analysis/PicardLindelof.v';
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
const LIP = '(forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2))';
const N_EX = 'picard_fixed_exists : forall N, exists y : nat -> Q, forall k, (k <= N)%nat -> picard_op f h y0 y k == y k (ProcessPicardGridSolution.v:243) — раздел Triangular: f, h, y0 произвольны; посылок нет (ни липшицевости, ни 0 <= h, ни L·T < 1). Свидетель — picard_fix N := picard_iter f h y0 (S N) (:211), итерация с номером N + 1. ' + CL + '.';
const N_FIX = 'picard_fix_is_fixed : forall N k, (k <= N)%nat -> picard_op f h y0 (picard_fix N) k = picard_fix N k (ProcessPicardGridSolution.v:213) — равенство Лейбница, для всякой правой части.';
const N_REACH = 'picard_iter_reaches_fix : forall (N m k : nat), (S N <= m)%nat -> (k <= N)%nat -> picard_iter f h y0 m k = picard_fix N k (ProcessPicardGridSolution.v:224) — начиная с номера N + 1 итерации совпадают с неподвижной точкой во всех узлах.';
const N_CONST = 'picard_iter_eventually_constant : forall (N m n k : nat), (S N <= m)%nat -> (S N <= n)%nat -> (k <= N)%nat -> picard_iter f h y0 m k = picard_iter f h y0 n k (ProcessPicardGridSolution.v:201) — равенство Лейбница; f, h, y0 произвольны (раздел Triangular). ' + CL + '.';
const N_EXT = "picard_fix_extends : forall N N' k, (N <= N')%nat -> (k <= N)%nat -> picard_fix N' k = picard_fix N k (ProcessPicardGridSolution.v:234) — шаг h один и тот же, меняется число узлов. " + CL + '.';
const N_ISEUL = 'picard_fixed_is_euler : forall N (y : nat -> Q), (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) -> y 0%nat == y0 ' + AND + ' forall k, (k < N)%nat -> y (S k) == y k + h * f (tgrid h k) (y k) (ProcessPicardGridSolution.v:252) — для всякой правой части; tgrid h k = k·h. ' + CL + '.';
const N_UNI = 'picard_unique_any_rate : forall (f : Q -> Q -> Q) (L : Q), ' + LIP + ' -> forall (h y0 : Q) (N : nat) (y z : nat -> Q), (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) -> (forall k, (k <= N)%nat -> picard_op f h y0 z k == z k) -> forall k, (k <= N)%nat -> y k == z k (ProcessPicardGridSolution.v:330). Посылок 0 < L, 0 <= h, L·T < 1 нет. Доказательство — picard_unique_triangular (:302), сильная индукция по узлу; от f нужно только согласие с == по второму аргументу (lipschitz_compat, :289). ' + CL + '.';
const N_EU = 'picard_grid_exists_unique : forall (f : Q -> Q -> Q) (L : Q), ' + LIP + ' -> forall (h y0 : Q) (N : nat), (forall k, (k <= N)%nat -> picard_op f h y0 (picard_fix f h y0 N) k == picard_fix f h y0 N k) ' + AND + ' (forall y : nat -> Q, (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) -> forall k, (k <= N)%nat -> y k == picard_fix f h y0 N k) (ProcessPicardGridSolution.v:342). Посылки на L·T нет.';
const N_EQE = 'picard_fixed_eq_euler : forall (f : Q -> Q -> Q) (h y0 : Q) (N : nat), (forall t y1 y2, y1 == y2 -> f t y1 == f t y2) -> forall y : nat -> Q, (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) -> forall k, (k <= N)%nat -> y k == ProcessODEStability.euler f h y0 k (ProcessPicardGridSolution.v:366); euler (ProcessODEStability.v:57) — ломаная Главы 8.4. Посылка — согласие f с равенством рациональных по второму аргументу. ' + CL + '.';
const N_EQT = 'picard_fix_eq_euler_traj : forall (f : Q -> Q -> Q) (y0 : Q) (N : nat), (forall t1 t2 y1 y2, t1 == t2 -> y1 == y2 -> f t1 y1 == f t2 y2) -> forall k, (k <= N)%nat -> picard_fix f (1 / inject_Z (Z.of_nat N)) y0 N k == PicardLindelof.euler_traj f y0 N k (ProcessPicardGridSolution.v:396); euler_traj (PicardLindelof.v:36) — ломаная Главы 8.2, шаг 1/N. ' + CL + '.';
const N_CAU = 'picard_iter_sup_cauchy : forall (f : Q -> Q -> Q) (L : Q), 0 < L -> ' + LIP + ' -> forall h, 0 <= h -> forall (y0 : Q) (N : nat), L * Tlen h N < 1 -> forall eps, 0 < eps -> exists M : nat, forall m n, (M <= m)%nat -> (M <= n)%nat -> forall k, (k <= N)%nat -> Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k) < eps (ProcessPicardGridSolution.v:611).';
const N_UNIF = 'picard_iter_modulus_uniform : forall (r C eps : Q), 0 <= r -> r < 1 -> 0 <= C -> 0 < eps -> exists M : nat, forall (f : Q -> Q -> Q) (L : Q), 0 < L -> ' + LIP + ' -> forall h, 0 <= h -> forall (y0 : Q) (N : nat), L * Tlen h N <= r -> (forall k, (k <= N)%nat -> Qabs (picard_iter f h y0 1 k - picard_iter f h y0 0 k) <= C) -> forall m n, (M <= m)%nat -> (M <= n)%nat -> forall k, (k <= N)%nat -> Qabs (picard_iter f h y0 m k - picard_iter f h y0 n k) < eps (ProcessPicardGridSolution.v:548). Номер M стоит до кванторов по f, L, h, y0 и N: он зависит только от r (оценки L·T сверху), C (оценки первого зазора) и eps.';
const N_GF = 'picard_iter_modulus_grid_free : forall (f : Q -> Q -> Q) (L F T y0 : Q), 0 < L -> ' + LIP + ' -> (forall t, Qabs (f t y0) <= F) -> 0 <= T -> L * T < 1 -> forall eps, 0 < eps -> exists M : nat, forall N : nat, (0 < N)%nat -> forall m n, (M <= m)%nat -> (M <= n)%nat -> forall k, (k <= N)%nat -> Qabs (picard_iter f (T / inject_Z (Z.of_nat N)) y0 m k - picard_iter f (T / inject_Z (Z.of_nat N)) y0 n k) < eps (ProcessPicardGridSolution.v:662). Шаг сетки h = T/N; номер M стоит до квантора по N. Первый зазор оценён числом T·F (picard_first_gap, :631).';
const N_CSUP = 'picard_op_contraction_sup : forall (f : Q -> Q -> Q) (L : Q), 0 < L -> ' + LIP + ' -> forall h, 0 <= h -> forall (y0 : Q) (N : nat) (y z : nat -> Q), gmax (fun k => Qabs (picard_op f h y0 y k - picard_op f h y0 z k)) N <= (L * Tlen h N) * gmax (fun k => Qabs (y k - z k)) N (ProcessPicardGridSolution.v:698); gmax — максимум по узлам 0…N (ProcessPicardOperator.v:156).';
const N_GSUP = 'picard_iter_gap_sup : forall (f : Q -> Q -> Q) (L : Q), 0 < L -> ' + LIP + ' -> forall h, 0 <= h -> forall (y0 : Q) (N n : nat), gmax (fun k => Qabs (picard_iter f h y0 (S n) k - picard_iter f h y0 n k)) N <= rpow L h N n * gmax (fun k => Qabs (picard_iter f h y0 1 k - picard_iter f h y0 0 k)) N (ProcessPicardGridSolution.v:714); rpow L h N n = (L·Tlen)^n (ProcessPicardOperator.v:216).';
const N_RATE = 'rate_attained : Qabs (picard_op f_lin 1 1 (fun _ => 1) 3 - picard_op f_lin 1 1 (fun _ => 0) 3) == (1 * Tlen 1 3) * 1 (ProcessPicardGridSolution.v:763); f_lin := fun _ y => y (:736), липшицева с L = 1 (f_lin_lipschitz, :738); rate_3_not_below_1 : ~ (1 * Tlen 1 3 < 1) (:742). Два постоянных кандидата (1 и 0) различаются на D = 1, их образы в узле 3 — ровно на L·T·D = 3.';
const N_VALS = 'fix_lin_values : picard_fix f_lin 1 1 3 0 == 1 ' + AND + ' picard_fix f_lin 1 1 3 1 == 2 ' + AND + ' picard_fix f_lin 1 1 3 2 == 4 ' + AND + ' picard_fix f_lin 1 1 3 3 == 8 (ProcessPicardGridSolution.v:746).';
const N_LUNI = 'fix_lin_unique : forall y : nat -> Q, (forall k, (k <= 3)%nat -> picard_op f_lin 1 1 y k == y k) -> forall k, (k <= 3)%nat -> y k == picard_fix f_lin 1 1 3 k (ProcessPicardGridSolution.v:751).';
const SEC = 'Посылки раздела Refinement (ProcessEulerRefinement.v:168–:175): g : Q -> Q (правая часть не зависит от t), 0 <= L, forall y1 y2, Qabs (g y1 - g y2) <= L * Qabs (y1 - y2), forall y, Qabs (g y) <= M.';
const N_REF = 'euler_refine_bound : forall (d : Q) (k : nat), 0 <= d -> Qabs (eul (2 * d) y0 k - eul d y0 (2 * k)) <= refine_bound d k (ProcessEulerRefinement.v:239), где eul := ProcessODEStability.euler (fun _ : Q => g) (:177), refine_bound d 0 = 0, refine_bound d (S k) = (1 + 2 * L * d) * refine_bound d k + L * M * d * d (:231). ' + SEC;
const N_TAIL = 'euler_dyadic_modulus_tail : forall T k0, 0 <= T -> L * T < inject_Z (Z.of_nat (S k0)) -> forall n m, (n <= m)%nat -> Qabs (euler_dyadic T m - euler_dyadic T n) <= 2 * ((L * M * T * T / 4) * growth_cap (L * T) k0) * half_pow n (ProcessEulerRefinement.v:422); euler_dyadic T j := eul (T * half_pow j) y0 (2 ^ j) (:298) — значение в момент T на сетке из 2^j шагов; half_pow n = (1/2)^n (:84); growth_cap s k0 := 1 / qpow (1 - s / (k0 + 1)) (k0 + 1) (:131) — потолок множителя роста (на странице B); k0 — любое натуральное с L·T < k0 + 1.';
const N_DCAU = 'euler_dyadic_is_Cauchy : forall T, 0 <= T -> is_Cauchy (euler_dyadic T) (ProcessEulerRefinement.v:439); is_Cauchy — ProcessCore.v:68 («для всякого eps > 0 найдётся номер…»).';
const N_TCAU = 'euler_traj_dyadic_is_Cauchy : is_Cauchy (fun j => PicardLindelof.euler_traj (fun _ : Q => g) y0 (2 ^ j) (2 ^ j)) (ProcessEulerRefinement.v:484) — ломаная Главы 8.2 на сетке из 2^j шагов в последнем узле (момент t = 1); связь двух определений ломаной — euler_traj_eq_euler (:149) и euler_traj_dyadic (:469).';
const N_CL1 = 'clamp1_dyadic_is_Cauchy : forall (y0 T : Q), 0 <= T -> is_Cauchy (euler_dyadic clamp1 y0 T) (ProcessEulerRefinement.v:539); clamp1 y — срезка y к отрезку [−1, 1] (:509): Qabs (clamp1 y) <= 1 (clamp1_bounded, :512), липшицева с константой 1 (clamp1_lipschitz, :519), на отрезке совпадает с y (clamp1_inside, :533) — правая часть не постоянная, L = 1, M = 1.';
const SIX = 'picard_op_contraction, picard_iter_gap, picard_unique (ProcessPicardOperator.v), picard_iter_sup_cauchy, picard_fixed_exists, picard_unique_any_rate (ProcessPicardGridSolution.v): ' + CL;
const NOFUN = 'Определения функции-решения на отрезке нет ни в одном из трёх файлов главы (ProcessPicardOperator.v, ProcessPicardGridSolution.v, ProcessEulerRefinement.v); шапки двух новых файлов называют это в разделе «NOT claimed» («a solution function on the interval as a limit over grid refinement»; «a limit function of the polygons»).';

// --- цитаты страницы после правок
const C14A = 'О самих ломаных: при автономной правой части, ограниченной и липшицевой, их значения в данный момент времени при удвоении сетки образуют процесс Коши с явным модулем.[^10]';
const C14B = 'И о втором процессе приближений, которому посвящена глава, — итерациях оператора Пикара на фиксированной сетке: на достаточно коротком интервале они сближаются геометрически, а их предел на сетке есть ломаная Эйлера той же сетки.[^11]';
const C50A = 'Чего глава *не* делает: она не строит функцию-решение на отрезке как завершённый объект.';
const C50B = L('На сетке всё доведено до конца, и без аксиом: *геометрический зазор* итератов доказан алгебраически; его *чтение* как $§varepsilon$-Коши-сходимости («для всякого $§varepsilon$ найдётся номер») опирается на затухание $(LT)^n§to 0$, которое над ℚ выводится из неравенства Бернулли и свойства Архимеда; а предел итераций на сетке — конечная грид-функция, на которой итерации останавливаются.');
const C55 = 'Роль-пределом остаётся завершённая функция-предел по измельчению сетки; этот шаг в этой главе не актуализируется.[^3]';
const C60 = L('*Первый* — сжатие оператора Пикара на грид-функциях, геометрический зазор итератов, их $§varepsilon$-сходимость, существование и единственность решения на сетке: доказаны над ℚ без аксиом.');
const C64 = '*Третий* — завершённая функция-решение на отрезке и глобальное решение — роль-пределы; в формализации этой главы их нет.';
const C186 = L('Подчеркнём честно: *геометрический зазор* доказан без аксиом, и без аксиом же доказан переход от него к самой Коши-сходимости в форме «для всякого $§varepsilon$ найдётся номер»: затухание $(LT)^n§to 0$ над ℚ следует из неравенства Бернулли и свойства Архимеда.');
const C189 = L('Номер этот определяется числами $LT$, оценкой первого зазора и $§varepsilon$; число узлов сетки в него не входит.');
const C207 = 'Существенно, что максимум берётся по *конечной* сетке: это рациональное число, а не предел, и потому единственность не требует L3.';
const C209 = 'Не требует его и *существование* решения на сетке: предел итераций — конечная грид-функция, предъявленная явно.';
const C219 = L('Оценка сжатия — *локальная*. Коэффициент сжатия есть $L§cdot T$, и режим, в котором оператор сжимает, — $L§cdot T < 1$, то есть интервал короче $1/L$.');
const C220 = L('На таком интервале процесс итераций Пикара — Коши с геометрическим зазором $(LT)^n$, причём номер, с которого итерации $§varepsilon$-близки, от числа узлов сетки не зависит.');
const C222 = 'Существование и единственность решения на сетке от длины интервала не зависят: оператор на сетке треуголен, неподвижная точка строится узел за узлом и достигается не позже чем за $N{+}1$ итерацию.[^12]';
const C232 = 'Это честная P4-граница: завершённое решение на неограниченном интервале — роль-предел, а теорема о продолжении — направление, а не построенный результат.';
const C236 = '*Режим $LT<1$ — не дефект, а условие оценки сжатия: при нём оператор сближает любые два кандидата в sup-метрике, и темп сближения итераций не зависит от мелкости сетки.';
const C238 = 'Само решение на сетке от этого режима не зависит: неподвижная точка существует и единственна на сетке любой длины.';
const C260 = L('Ни сжатие, ни зазор, ни $§varepsilon$-сходимость итераций, ни существование и единственность неподвижной точки на сетке L3 не требуют: это алгебраические факты о конечных суммах.');
const C268 = 'Неподвижная точка на сетке — роль-решение, и она актуальна: это конечная грид-функция, на которой итерации останавливаются.';
const C292 = 'Именно эта конечность арены делает доказанным всё, что сказано о сетке (сжатие, зазор, сходимость итераций, существование и единственность — 0 аксиом), и отделяет его от границы (завершённая функция-решение на отрезке — роль-предел).';
const F1 = L('`euler_picard_contraction` в `ProcessPicard.v`: при правой части, липшицевой и ограниченной на всём ℚ ($§lvert g§rvert§le M$), отображение $y§mapsto y_0+g(y)h$ есть сжатие отрезка $[y_0-Mh,§,y_0+Mh]$ с коэффициентом $Lh$ при $Lh<1$; сама оценка — расстояние между образами не превосходит $Lh$, умноженного на расстояние между числами, — верна на всём ℚ и без ограниченности (`euler_picard_lip`).');
const F2A = 'Опорные файлы (Rocq-репозиторий ToS). `ProcessPicardOperator.v`: оператор Пикара на грид-функциях, теорема о сжатии в sup-метрике (`picard_op_contraction`), геометрический зазор итератов (`picard_iter_gap`) и единственность решения на сетке (`picard_unique`).';
const F2B = '`ProcessPicardGridSolution.v`: существование решения на сетке (`picard_fixed_exists`), его единственность при любом $LT$ (`picard_unique_any_rate`), сходимость итераций (`picard_iter_sup_cauchy`) и связь с ломаной Эйлера (`picard_fixed_is_euler`).';
const F2C = 'Все теоремы обоих файлов — 0 аксиом (`Print Assumptions`: «closed under the global context»).';
const F3A = 'Сходимость итераций оператора — `picard_iter_sup_cauchy` в `ProcessPicardGridSolution.v` — идёт через зазор `picard_iter_gap` и затухание `Qpow_vanish` (`SeriesConvergence.v`).';
const F3B = 'Неподвижная точка на сетке — `picard_fix`: это итерация с номером $N{+}1$, и все следующие с ней совпадают (`picard_fix_is_fixed`, `picard_iter_reaches_fix`).';
const F3C = 'Сжатие, зазор, сходимость, существование и единственность — 0 аксиом (проверено `Print Assumptions`); функция-решение на отрезке — роль-предел.';
const F6B = 'В записи через максимум по узлам — `picard_op_contraction_sup` в `ProcessPicardGridSolution.v`.';
const F7A = L('`picard_iter_gap` в `ProcessPicardOperator.v`: $§supnorm{§Phi^{n+1}-§Phi^n}§le (L§cdot T)^n C_0$, где $C_0$ — оценка первого зазора; доказано индукцией по $n$ через теорему о сжатии; в записи через максимум по узлам — `picard_iter_gap_sup` в `ProcessPicardGridSolution.v`.');
const F7B = L('Сходимость в форме «для всякого $§varepsilon$ найдётся номер» — `picard_iter_sup_cauchy` там же; номер, в который число узлов не входит, — `picard_iter_modulus_uniform`. 0 аксиом.');
const F8A = L('Максимум по конечной сетке реализован как `gmax` — наибольшее из $N{+}1$ рациональных значений; отсюда $D^*§le(LT)D^*$ и $LT<1$ дают $D^*=0$ *без* обращения к пределу.');
const F8B = 'Посылка $LT<1$ нужна этому доказательству, но не самому утверждению: `picard_unique_any_rate` в `ProcessPicardGridSolution.v` — единственность при любом $LT$, индукцией по узлу; `picard_grid_exists_unique` — существование и единственность вместе. 0 аксиом.';
const F10A = L('`euler_refine_bound`: ломаная с шагом $2d$ в узле $k$ и ломаная с шагом $d$ в узле $2k$ (один и тот же момент времени) различаются не больше чем на $e_k$, где $e_0 = 0$, $e_{k+1} = (1+2Ld)§,e_k + LMd^2$.');
const F10B = L('`euler_dyadic_modulus_tail`: значения в момент $T$ на сетках из $2^n$ и $2^m$ шагов, $n §le m$, различаются не больше чем на $2K/2^n$, $K = §tfrac{LMT^2}{4}§,B$, где $B$ — общий для всех сеток потолок множителя роста.');
const F10C = '`euler_dyadic_is_Cauchy`: эти значения — процесс Коши; `euler_traj_dyadic_is_Cauchy` — то же для `euler_traj` Главы 8.2 в момент $t = 1$.';
const F10D = L("Посылки: правая часть не зависит от $t$, липшицева и ограничена на всём ℚ ($§lvert g§rvert §le M$); уравнение $y' = y$ под них не подпадает — для него сближение стадий доказано отдельно (Глава 8.2, `exp1_is_Cauchy`).");
const F10E = 'Что посылки выполнимы при $L > 0$ — `clamp1_dyadic_is_Cauchy`. 0 аксиом (проверено `Print Assumptions`).';
const F11A = '`picard_fixed_is_euler` в `ProcessPicardGridSolution.v`: у всякой неподвижной точки оператора на сетке значение в нулевом узле равно начальному, а $y_{k+1} = y_k + h f(t_k, y_k)$.';
const F11B = 'Совпадение с ломаными Глав 8.4 и 8.2 — `picard_fixed_eq_euler` и `picard_fix_eq_euler_traj`. 0 аксиом.';
const F12A = '`picard_grid_exists_unique`: при липшицевой правой части неподвижная точка на сетке существует и единственна при любом $LT$.';
const F12B = '`picard_iter_eventually_constant`: начиная с номера $N{+}1$ все итерации совпадают во всех узлах — для всякой правой части.';
const F12C = '`picard_fix_extends`: решение на более длинной сетке совпадает с решением на более короткой во всех её узлах.';
const F12D = L('`picard_iter_modulus_grid_free`: при $LT<1$ и $§lvert f(t, y_0)§rvert §le F$ номер, с которого итерации $§varepsilon$-близки, выбирается до числа узлов $N$.');
const F12E = "`rate_attained`: при $y' = y$, $h = 1$, $N = 3$ ($LT = 3$) коэффициент $LT$ достигается, а неподвижная точка $(1, 2, 4, 8)$ существует и единственна (`fix_lin_values`, `fix_lin_unique`). 0 аксиом.";

{
  const { fix, add, save } = open('part08-ch03');

  // ------------------------------------------------------------ «Гарантия сходимости» (место 3.3)
  fix('Ломаная Эйлера — это последовательность рациональных стадий', 'picard_iter_gap', { theorem: 'euler_dyadic_is_Cauchy', file: ER, assumptions: CL,
    note: DONE + ' (формализацией и добавлением к абзацу; сама фраза не менялась): вопрос был о стадиях ломаной Эйлера, а теоремы главы — об итерациях оператора при одной сетке. Теперь ответ на вопрос о самих ломаных доказан: ' + N_DCAU + ' ' + SEC + ' Эти посылки страница называет следующей фразой и в сноске 10; для y′ = y — лестница Главы 8.2 (exp1_is_Cauchy, ProcessExpLadder.v:729).' });
  add({ theorem: 'euler_dyadic_modulus_tail', file: ER, assumptions: CL, claim: C14A,
    note: DONE + ': новая фраза. «С явным модулем»: ' + N_TAIL + ' Свойство Коши — ' + N_DCAU + ' Оценка одного удвоения — ' + N_REF });
  add({ theorem: 'picard_iter_gap', file: PO, assumptions: CL, claim: C14B,
    note: DONE + ': новая фраза. «Сближаются геометрически»: picard_iter_gap (ProcessPicardOperator.v:234) — зазор соседних итераций не больше rpow n * C, rpow n = (L·Tlen)^n. «На достаточно коротком интервале» — при L·T < 1: степени убывают, и итерации ε-сходятся: ' + N_CAU });
  add({ theorem: 'picard_fixed_is_euler', file: GS, assumptions: CL, claim: C14B,
    note: '«Их предел на сетке есть ломаная Эйлера той же сетки»: итерации с номера N + 1 совпадают с неподвижной точкой (' + N_REACH + '), а всякая неподвижная точка есть ломаная: ' + N_ISEUL + ' Совпадение с определениями ломаной в Главах 8.4 и 8.2 — picard_fixed_eq_euler (:366), picard_fix_eq_euler_traj (:396).' });

  // ------------------------------------------------------------ «Что эта глава утверждает — и что нет» (место 3.1)
  fix('Предыдущий слой формализации тома', 'euler_picard_contraction', {
    note: 'euler_picard_contraction (ProcessPicard.v:165): is_contraction (euler_picard g y0 h) (y0 − M·h) (y0 + M·h) (L·h); euler_picard g y0 h y := y0 + g y * h (:115). Условия теоремы (ограниченность правой части, отрезок) страница называет в сноске 1.' });
  fix('Настоящая глава предъявляет именно теорему', 'picard_op_contraction', {
    note: 'Доказаны оценка сжатия (picard_op_contraction, ProcessPicardOperator.v:102), зазор итераций (picard_iter_gap, :234) и единственность при L·Tlen < 1 (picard_unique, :183) для функций nat -> Q на узлах k ≤ N. Что «пространство функций» здесь — значения в N+1 узле, страница оговаривает следующим абзацем. С 19.11 доказаны и существование неподвижной точки на сетке, и ε-сходимость итераций (ProcessPicardGridSolution.v: picard_fixed_exists, :243; picard_iter_sup_cauchy, :611); функция-решение на отрезке не строится — страница говорит это там же.' });
  add({ theorem: null, file: GS, claim: C50A,
    note: DONE + ': новая первая фраза абзаца. Статус честный. ' + NOFUN });
  fix('Чего глава *не* делает: *геометрический зазор*', 'Qpow_vanish', { claim: C50B, assumptions: CL, page_price: 'без аксиом',
    note: DONE + ': абзац переписан — слова «эти два шага наследуют закон исключённого третьего» сняты. Затухание: Qpow_vanish : forall r eps, 0 < r -> r < 1 -> 0 < eps -> exists N, Qpow r N < eps (SeriesConvergence.v:164); доказательство — через bernoulli_ineq и nat_archimedean того же файла. ' + CL + '.' });
  add({ theorem: 'picard_iter_sup_cauchy', file: GS, assumptions: CL, claim: C50B, page_price: 'без аксиом',
    note: '«Чтение как ε-Коши-сходимости» — теорема: ' + N_CAU + ' ' + CL + '.' });
  add({ theorem: 'picard_iter_reaches_fix', file: GS, assumptions: CL, claim: C50B, page_price: 'без аксиом',
    note: '«Предел итераций на сетке — конечная грид-функция, на которой итерации останавливаются»: ' + N_REACH + ' ' + N_FIX + ' Обе — ' + CL + '.' });
  add({ theorem: null, file: ER, claim: C55,
    note: 'Статус честный. О пределе по измельчению сетки доказано свойство процесса значений: значения ломаных в данный момент времени при удвоении сетки — процесс Коши (euler_dyadic_is_Cauchy, ProcessEulerRefinement.v:439; посылки — автономная, ограниченная, липшицева правая часть). Функция-предел как объект не определена. ' + NOFUN });
  fix('*Первый* — сжатие оператора Пикара на грид-функциях, геометрический зазор итератов и единственность', null, { claim: C60, page_price: 'без аксиом', assumptions: SIX,
    note: DONE + ': в перечень первого уровня добавлены ε-сходимость итераций и существование решения на сетке. Сжатие — picard_op_contraction (ProcessPicardOperator.v:102); зазор — picard_iter_gap (:234); ε-сходимость — picard_iter_sup_cauchy (ProcessPicardGridSolution.v:611); существование — picard_fixed_exists (:243); единственность — picard_unique (ProcessPicardOperator.v:183) и picard_unique_any_rate (ProcessPicardGridSolution.v:330).' });
  fix('*Третий* — завершённый предел', null, { claim: C64, page_price: '',
    note: DONE + ' (вопрос 1, вариант 1): слово «L3-слой» снято — цену того, чего в формализации нет, компилятор не показывает. Теорем о функции-решении на отрезке и о глобальном решении нет. ' + NOFUN });

  // ------------------------------------------------------------ E/R/R-каркас, оператор, сжатие — уточнение заметок
  fix(L('Оператор Пикара на сетке $§Phi(y)_k'), null, {
    note: 'picard_op (ProcessPicardOperator.v:63), Tlen (:57), picard_op_contraction (:102), picard_iter_gap (:234; множитель rpow n = (L·Tlen)^n, :216), picard_unique (:183, посылка Hrate : L * Tlen < 1). Единственность на сетке верна и без посылки L·T < 1 — picard_unique_any_rate (ProcessPicardGridSolution.v:330); страница говорит это в разделе «Локальное существование и его граница» и в сноске 8.' });
  fix('Расстояние между двумя кандидатами', 'gmax', {
    note: 'Максимум по узлам 0…N — gmax (ProcessPicardOperator.v:156) с леммами gmax_ub (:159), gmax_lub (:168). Отдельного определения расстояния между функциями нет: теорема о сжатии записана через общую оценку D. Запись сжатия и зазора прямо через максимум — picard_op_contraction_sup (ProcessPicardGridSolution.v:698), picard_iter_gap_sup (:714); обе названы в сносках 6 и 7.' });

  // ------------------------------------------------------------ «Итераты сближаются геометрически» (место 3.1)
  fix('Запустим процесс с постоянной функции', 'picard_iter_gap', {
    note: 'picard_iter 0 = fun _ => y0, picard_iter (S n) = picard_op (picard_iter n) (ProcessPicardOperator.v:213). picard_iter_gap (:234): если Qabs (picard_iter 1 k − picard_iter 0 k) <= C при k ≤ N, то Qabs (picard_iter (S n) k − picard_iter n k) <= rpow n * C при k ≤ N; условие L·T < 1 теореме не нужно. Запись через максимум (формула страницы): ' + N_GSUP });
  fix('При $LT<1$ степени $(LT)^n$ убывают', 'picard_iter_gap', {
    note: 'Зазор соседних итераций — picard_iter_gap (ProcessPicardOperator.v:234). Утверждение «для всякого ε найдётся номер» с 19.11 — теорема: ' + N_CAU + ' Страница говорит это следующей фразой и в сноске 7.' });
  fix('Подчеркнём честно: *геометрический зазор* доказан без аксиом; переход', 'Qpow_vanish', { claim: C186, assumptions: CL, page_price: 'без аксиом',
    note: DONE + ': слова «использует затухание, наследующее L3» сняты. Qpow_vanish (SeriesConvergence.v:164): forall r eps, 0 < r -> r < 1 -> 0 < eps -> exists N, Qpow r N < eps — через bernoulli_ineq и nat_archimedean; ' + CL + '.' });
  add({ theorem: 'picard_iter_sup_cauchy', file: GS, assumptions: CL, claim: C186, page_price: 'без аксиом',
    note: 'Переход от зазора к ε-сходимости — теорема: ' + N_CAU + ' Доказательство: телескопическая сумма зазоров (picard_iter_tel, :465; picard_iter_tail, :517) и малость хвоста геометрической прогрессии (geom_tail_small, :438 — через Qpow_vanish). ' + CL + '.' });
  add({ theorem: 'picard_iter_modulus_uniform', file: GS, assumptions: CL, claim: C189,
    note: DONE + ': новая фраза. ' + N_UNIF + ' ' + CL + '. В форме «шаг h = T/N, номер выбран до N» — picard_iter_modulus_grid_free (:662).' });

  // ------------------------------------------------------------ «Решение единственно — без аксиом»
  fix('При $LT<1$ это возможно лишь при', 'picard_unique', {
    note: 'Так и идёт доказательство picard_unique (ProcessPicardOperator.v:189–207): Dstar := gmax (fun j => Qabs (y j − z j)) N, Dstar <= (L * Tlen) * Dstar, откуда Dstar == 0. Заключение теоремы верно и без посылки L·T < 1 — picard_unique_any_rate (ProcessPicardGridSolution.v:330); сноска 8 говорит это прямо.' });
  fix('Существенно, что максимум берётся по *конечной* сетке', null, { claim: C207, theorem: 'picard_unique', assumptions: CL, page_price: 'единственность не требует L3',
    note: DONE + ': конец фразы («в отличие от существования завершённого предела») заменён следующей фразой — о существовании. picard_unique (ProcessPicardOperator.v:183): ' + CL + '.' });
  add({ theorem: 'picard_fixed_exists', file: GS, assumptions: CL, claim: C209, page_price: 'существование не требует L3',
    note: DONE + ': новая фраза. ' + N_EX + ' «Предъявленная явно» — свидетель picard_fix N.' });

  // ------------------------------------------------------------ «Локальное существование и его граница» (место 3.2)
  fix('Теорема главы — *локальная*', 'picard_unique', { claim: C219, theorem: 'picard_op_contraction', assumptions: CL,
    note: DONE + ' (вопрос 2, вариант 1): локальной названа оценка сжатия, а не существование и единственность. picard_op_contraction (ProcessPicardOperator.v:102): оценка с множителем L * Tlen верна при любом его значении; сжатием она служит при L·T < 1. Что множитель достигается (и при L·T > 1 оператор в sup-метрике не сжимает) — пример: ' + N_RATE });
  fix('На таком интервале процесс итераций Пикара — Коши (геометрический зазор)', null, { claim: C220, theorem: 'picard_iter_modulus_grid_free', file: GS, assumptions: CL,
    note: DONE + ': вместо слов о «локальном существовании и единственности» — сходимость итераций с номером, не зависящим от сетки. ' + N_GF + ' ' + CL + '.' });
  add({ theorem: 'picard_grid_exists_unique', file: GS, assumptions: CL, claim: C222,
    note: DONE + ': новая фраза. ' + N_EU + ' ' + CL + '.' });
  add({ theorem: 'picard_iter_reaches_fix', file: GS, assumptions: CL, claim: C222,
    note: '«Достигается не позже чем за N+1 итерацию»: ' + N_REACH + ' «Оператор на сетке треуголен»: picard_op_ext_eq (:163) — значение образа в узле k зависит только от значений в узлах j < k; «строится узел за узлом»: picard_iter_stable (:175) — в узле k итерации перестают меняться с номера k + 1.' });
  fix('Но глобальная картина', null, {
    note: 'Статус назван честно: теорем о продолжении функции-решения на всё время, о максимальном интервале и об уходе в бесконечность нет ни в ProcessPicardOperator.v, ни в ProcessPicardGridSolution.v, ProcessEulerRefinement.v, ProcessPicard.v, ProcessODE.v, ProcessODEStability.v, analysis/PicardLindelof.v; шапка ProcessPicardGridSolution.v называет это в разделе «NOT claimed» («global continuation, blow-up, the maximal interval of existence»). На сетке с данным шагом продолжение — теорема (picard_fix_extends, ProcessPicardGridSolution.v:234), но это свойство ломаной, а не глобальная картина функции-решения.' });
  add({ theorem: null, file: GS, claim: C232,
    note: 'Фраза оставлена: она о завершённом решении на неограниченном интервале и о классической теореме о продолжении функции-решения. На сетке с данным шагом продолжение доказано и названо в сноске 12: ' + N_EXT + ' Неподвижная точка существует при всяком N (picard_fixed_exists, :243). Теоремы о продолжении для функции-решения в формализации нет.' });
  fix('*Локальность — не дефект', 'picard_unique', { claim: C236, theorem: 'picard_op_contraction_sup', file: GS, assumptions: CL,
    note: DONE + ': курсив переписан — режим L·T < 1 назван условием оценки сжатия, а не содержанием теоремы. «Сближает любые два кандидата в sup-метрике»: ' + N_CSUP + ' ' + CL + '.' });
  add({ theorem: 'picard_iter_modulus_grid_free', file: GS, assumptions: CL, claim: C236,
    note: '«Темп сближения итераций не зависит от мелкости сетки»: ' + N_GF + ' ' + CL + '.' });
  add({ theorem: 'picard_grid_exists_unique', file: GS, assumptions: CL, claim: C238,
    note: DONE + ': новая фраза. ' + N_EU + ' Пример вне режима L·T < 1 (y′ = y, h = 1, N = 3, L·T = 3): fix_lin_values (:746), fix_lin_unique (:751). ' + CL + '.' });

  // ------------------------------------------------------------ E/R/R-разбор (места 3.1; вопрос 3)
  fix('Универсальный слой включает L3', null, { claim: C260, page_price: 'L3 не требуют', assumptions: SIX,
    note: DONE + ' (вопрос 1, вариант 1): фраза «универсальный слой включает L3 там, где…» снята. Все шесть теорем — ' + CL + '; classic не входит в допущения ни одного объявления трёх файлов главы (ProcessPicardOperator.v — 19 объявлений, ProcessPicardGridSolution.v — 46, ProcessEulerRefinement.v — 36).' });
  add({ theorem: 'picard_fix_is_fixed', file: GS, assumptions: CL, claim: C268,
    note: DONE + ' (вопрос 3, вариант 1): неподвижная точка на сетке названа актуальной. ' + N_FIX + ' ' + N_REACH + ' Роль-пределом названа функция-решение на отрезке — её в формализации нет.' });
  fix('Именно эта конечность арены отделяет', null, { claim: C292, page_price: '0 аксиом', assumptions: SIX,
    note: DONE + ' (вопрос 1, вариант 1): перечень доказанного дополнен сходимостью итераций и существованием; граница названа роль-пределом, без слова «L3-слой». ' + NOFUN });

  // ------------------------------------------------------------ сноска 1 (место 3.4)
  fix('`euler_picard_contraction` в `ProcessPicard.v`: сжатие отображения', 'euler_picard_contraction', { claim: F1, assumptions: CL,
    note: DONE + ': в сноску внесены посылки теоремы. euler_picard_contraction : forall g y0 h L M, 0 <= h -> is_lipschitz_auto g L -> is_bounded_auto g M -> L * h < 1 -> is_contraction (euler_picard g y0 h) (y0 - M * h) (y0 + M * h) (L * h) (ProcessPicard.v:165); is_bounded_auto g M — правая часть ограничена на всём ℚ. Для y′ = y посылка не выполняется; теорема об этом — на шаге 3 (глава VIII.1).' });
  add({ theorem: 'euler_picard_lip', file: PP, assumptions: CL, claim: F1,
    note: DONE + ': названа оценка без ограниченности. euler_picard_lip : forall g y0 h L y1 y2, 0 <= h -> is_lipschitz_auto g L -> Qabs (euler_picard g y0 h y1 - euler_picard g y0 h y2) <= (L * h) * Qabs (y1 - y2) (ProcessPicard.v:149) — на всём ℚ; посылок об ограниченности и о L·h < 1 нет. ' + CL + '.' });

  // ------------------------------------------------------------ сноска 2
  fix('Опорный файл — `ProcessPicardOperator.v`', 'picard_op_contraction', { claim: F2A,
    note: DONE + ': сноска называет два опорных файла. Три теоремы первого: picard_op_contraction (ProcessPicardOperator.v:102), picard_iter_gap (:234), picard_unique (:183).' });
  add({ theorem: 'picard_fixed_exists', file: GS, assumptions: CL, claim: F2B, note: DONE + ': новый файл назван. ' + N_EX });
  add({ theorem: 'picard_unique_any_rate', file: GS, assumptions: CL, claim: F2B, note: N_UNI });
  add({ theorem: 'picard_iter_sup_cauchy', file: GS, assumptions: CL, claim: F2B, note: N_CAU + ' ' + CL + '.' });
  add({ theorem: 'picard_fixed_is_euler', file: GS, assumptions: CL, claim: F2B, note: N_ISEUL });
  fix('Ключевые теоремы — 0 аксиом', null, { claim: F2C, page_price: '0 аксиом',
    assumptions: 'все объявления двух файлов (ProcessPicardOperator.v — 19 объявлений, ProcessPicardGridSolution.v — 46 объявлений): ' + CL,
    note: DONE + ': «ключевые теоремы» заменены на «все теоремы обоих файлов». ProcessPicardOperator.v — 11 Qed и 8 определений; ProcessPicardGridSolution.v — 44 Qed и 2 определения; строк Axiom, Parameter, Admitted нет. Print Assumptions всех объявлений — ' + CL + ' (первый файл — tools/tom-pa.cjs; второй — _p08step2/VerifyA.v).' });

  // ------------------------------------------------------------ сноска 3 (место 3.1)
  fix('Обёртка «итераты сходятся к пределу»', 'iterate_is_cauchy', { claim: F3A, theorem: 'picard_iter_sup_cauchy', file: GS, assumptions: CL, page_price: '',
    note: DONE + ': сноска переписана. Прежняя называла опорой iterate_is_cauchy (FixedPoint.v:263) — лемму о сжатии f : Q -> Q, к оператору на грид-функциях по типу не применимую, — и приписывала ей classic (компилятор: ' + CL + '). Теперь названа теорема о самих итерациях оператора: ' + N_CAU + ' ' + CL + '.' });
  fix('Обёртка «итераты сходятся к пределу»', 'Qpow_vanish', { claim: F3A, assumptions: CL, page_price: '',
    note: DONE + ': файл назван верно (SeriesConvergence.v:164, а не FixedPoint.v), слова «наследующие classic» сняты. Qpow_vanish : forall r eps, 0 < r -> r < 1 -> 0 < eps -> exists N, Qpow r N < eps; ' + CL + '. В доказательстве сходимости — через geom_tail_small (ProcessPicardGridSolution.v:438, вызов :447).' });
  add({ theorem: 'picard_iter_gap', file: PO, assumptions: CL, claim: F3A,
    note: 'Зазор соседних итераций: picard_iter_gap (ProcessPicardOperator.v:234); в доказательстве сходимости — в picard_iter_tel (ProcessPicardGridSolution.v:465, вызов :492). ' + CL + '.' });
  add({ theorem: 'picard_fix', file: GS, assumptions: CL, claim: F3B,
    note: DONE + ': новая фраза. Definition picard_fix (N : nat) : nat -> Q := picard_iter f h y0 (S N) (ProcessPicardGridSolution.v:211) — итерация с номером N + 1.' });
  add({ theorem: 'picard_fix_is_fixed', file: GS, assumptions: CL, claim: F3B, note: N_FIX + ' ' + CL + '.' });
  add({ theorem: 'picard_iter_reaches_fix', file: GS, assumptions: CL, claim: F3B, note: '«Все следующие с ней совпадают»: ' + N_REACH + ' ' + CL + '.' });
  fix('Сжатие, зазор и единственность — 0 аксиом; предел', 'classic', { claim: F3C, theorem: null, file: GS, external: undefined, page_price: '0 аксиом', assumptions: SIX,
    note: DONE + ' (вопрос 1, вариант 1): слова «предел — L3-слой» сняты; слово classic на странице больше не стоит. Пять названных свойств: сжатие — picard_op_contraction; зазор — picard_iter_gap; сходимость — picard_iter_sup_cauchy; существование — picard_fixed_exists; единственность — picard_unique, picard_unique_any_rate. Все — ' + CL + '. ' + NOFUN });

  // ------------------------------------------------------------ сноски 6, 7, 8
  add({ theorem: 'picard_op_contraction_sup', file: GS, assumptions: CL, claim: F6B, note: DONE + ': добавлена запись через максимум. ' + N_CSUP + ' ' + CL + '.' });
  fix('`picard_iter_gap` в `ProcessPicardOperator.v`: ', 'picard_iter_gap', { claim: F7A,
    note: 'picard_iter_gap (ProcessPicardOperator.v:234): индукция по n (:240), шаг — picard_op_contraction (:245); оценка поузловая при k ≤ N, множитель rpow n (:216). ' + CL + '. С 19.11 сноска называет и запись через максимум (формула страницы).' });
  add({ theorem: 'picard_iter_gap_sup', file: GS, assumptions: CL, claim: F7A, note: DONE + ': добавлена запись через максимум. ' + N_GSUP + ' ' + CL + '.' });
  add({ theorem: 'picard_iter_sup_cauchy', file: GS, assumptions: CL, claim: F7B, page_price: '0 аксиом', note: DONE + ': новая фраза сноски. ' + N_CAU + ' ' + CL + '.' });
  add({ theorem: 'picard_iter_modulus_uniform', file: GS, assumptions: CL, claim: F7B, page_price: '0 аксиом', note: N_UNIF + ' ' + CL + '.' });
  fix('Максимум по конечной сетке реализован как `gmax`', 'gmax', { claim: F8A });
  add({ theorem: 'picard_unique_any_rate', file: GS, assumptions: CL, claim: F8B, page_price: '0 аксиом',
    note: DONE + ': новая фраза сноски. ' + N_UNI });
  add({ theorem: 'picard_grid_exists_unique', file: GS, assumptions: CL, claim: F8B, page_price: '0 аксиом', note: N_EU + ' ' + CL + '.' });

  // ------------------------------------------------------------ сноска 10 (место 3.3)
  add({ theorem: 'euler_refine_bound', file: ER, assumptions: CL, claim: F10A,
    note: DONE + ': новая сноска. ' + N_REF + ' Узел k сетки с шагом 2d и узел 2k сетки с шагом d — один момент времени 2dk. ' + CL + '.' });
  add({ theorem: 'euler_dyadic_modulus_tail', file: ER, assumptions: CL, claim: F10B,
    note: N_TAIL + ' На странице K = (L·M·T²/4)·B; оценка 2K/2^n — в точности правая часть. ' + SEC + ' ' + CL + '.' });
  add({ theorem: 'euler_dyadic_is_Cauchy', file: ER, assumptions: CL, claim: F10C, note: N_DCAU + ' ' + SEC + ' ' + CL + '.' });
  add({ theorem: 'euler_traj_dyadic_is_Cauchy', file: ER, assumptions: CL, claim: F10C, note: N_TCAU + ' ' + CL + '.' });
  add({ theorem: 'euler_traj', file: PL, assumptions: CL, claim: F10C,
    note: 'Fixpoint euler_traj (PicardLindelof.v:36) — ломаная Главы 8.2: шаг 1/N, узлы k/N. Связь с ломаной ProcessODEStability.euler — euler_traj_eq_euler : forall (f : Q -> Q -> Q) (y0 : Q) (N k : nat), (forall t1 t2 y1 y2, t1 == t2 -> y1 == y2 -> f t1 y1 == f t2 y2) -> PicardLindelof.euler_traj f y0 N k == ProcessODEStability.euler f (1 / inject_Z (Z.of_nat N)) y0 k (ProcessEulerRefinement.v:149).' });
  add({ theorem: 'exp1_is_Cauchy', file: EL, assumptions: CL, claim: F10D,
    note: 'Посылки названы по разделу Refinement: ' + SEC + ' Для y′ = y правая часть g(y) = y не ограничена на ℚ — под посылку Hbd не подпадает; шапка файла говорит это в разделе «NOT claimed». Сближение стадий для y′ = y: exp1_is_Cauchy : is_Cauchy exp1_process (ProcessExpLadder.v:729) — стадии (1 + 1/N)^N, рост N на единицу (а не удвоение). ' + CL + '.' });
  add({ theorem: 'clamp1_dyadic_is_Cauchy', file: ER, assumptions: CL, claim: F10E, page_price: '0 аксиом', note: N_CL1 + ' ' + CL + '.' });
  add({ theorem: null, file: ER, claim: F10E, page_price: '0 аксиом',
    assumptions: 'все объявления файла (ProcessEulerRefinement.v — 36 объявлений): ' + CL,
    note: DONE + ': новый файл назван в сноске 10. src/process/ProcessEulerRefinement.v — 31 Qed и 5 определений (half_pow, growth_cap, refine_bound, euler_dyadic, clamp1); строк Axiom, Parameter, Admitted нет. Print Assumptions всех объявлений — ' + CL + ' (_p08step2/VerifyB.v).' });

  // ------------------------------------------------------------ сноска 11
  add({ theorem: 'picard_fixed_is_euler', file: GS, assumptions: CL, claim: F11A, note: DONE + ': новая сноска. ' + N_ISEUL });
  add({ theorem: 'picard_fixed_eq_euler', file: GS, assumptions: CL, claim: F11B, page_price: '0 аксиом', note: N_EQE });
  add({ theorem: 'picard_fix_eq_euler_traj', file: GS, assumptions: CL, claim: F11B, page_price: '0 аксиом', note: N_EQT });

  // ------------------------------------------------------------ сноска 12 (место 3.2)
  add({ theorem: 'picard_grid_exists_unique', file: GS, assumptions: CL, claim: F12A, note: DONE + ': новая сноска. ' + N_EU + ' ' + CL + '.' });
  add({ theorem: 'picard_iter_eventually_constant', file: GS, assumptions: CL, claim: F12B, note: N_CONST });
  add({ theorem: 'picard_fix_extends', file: GS, assumptions: CL, claim: F12C, note: N_EXT });
  add({ theorem: 'picard_iter_modulus_grid_free', file: GS, assumptions: CL, claim: F12D, note: N_GF + ' ' + CL + '.' });
  add({ theorem: 'rate_attained', file: GS, assumptions: CL, claim: F12E, page_price: '0 аксиом', note: N_RATE + ' ' + CL + '.' });
  add({ theorem: 'fix_lin_values', file: GS, assumptions: CL, claim: F12E, page_price: '0 аксиом', note: N_VALS + ' ' + CL + '.' });
  add({ theorem: 'fix_lin_unique', file: GS, assumptions: CL, claim: F12E, page_price: '0 аксиом', note: N_LUNI + ' ' + CL + '.' });

  save();
}
