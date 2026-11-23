// Часть VIII, шаг 4, страницы (2026-11-20, слово автора «делай»): 14 правок главы VIII.4 внесены
// (советуемые варианты трёх вопросов: слово об L3 в разборе оставлено один раз и отнесено к Главе 8.1,
// § «Где появляется граница»; курсив о двух режимах уточнён условием |alpha| h <= 1; время в отсылке к
// Главе 8.5 поправлено).
// Формализация — новый src/process/ProcessGronwallInequality.v; прежние файлы не менялись.
// Запуск: node patch-p08-step-04-pages.cjs  (затем relocate + merge по part08-ch04). Скрипт повторяем.
// Внимание: L() превращает знак «¤» в обратную косую черту; настоящий знак параграфа пишется прямо.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 20.11 (Часть VIII, шаг 4, слово автора)';
const KEPT = DONE + ' (формализацией; текст фразы не менялся): ';
const CL = 'Closed under the global context';
const GI = 'src/process/ProcessGronwallInequality.v';
const EL = 'src/process/ProcessExpLadder.v';
const GS = 'src/process/ProcessPicardGridSolution.v';
const PO = 'src/process/ProcessPicardOperator.v';
const OS = 'src/process/ProcessODEStability.v';
const PG = 'src/process/ProcessGronwall.v';
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
  const claimOf = (prefix) => {
    const r = j.records.find((x) => norm(x.claim).startsWith(prefix));
    if (!r) throw new Error(name + ': нет записи с началом: ' + prefix);
    return r.claim;
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
  return { j, fix, add, save, claimOf };
}

// --- утверждения (номера строк — по src)
const PREM = 'Посылки раздела StabilityIsGronwall: 0 <= L, липшицевость f по второму аргументу с константой L, 0 <= h.';
const N_GI = 'gronwall_inequality : forall alpha beta h (u : nat -> Q), 0 <= 1 + alpha * h -> (forall n, u (S n) <= (1 + alpha * h) * u n + beta * h) -> forall n, u n <= gronwall_iterate alpha beta h (u 0) n (ProcessGronwallInequality.v:104); с отдельным началом u 0 <= u0 — gronwall_inequality_from (:90). Последовательность u произвольна; условие на множитель существенно — gronwall_inequality_needs_nonneg_factor (:174). ' + CL + '.';
const N_HOM = 'gronwall_inequality_hom : forall alpha h (u : nat -> Q), 0 <= 1 + alpha * h -> (forall n, u (S n) <= (1 + alpha * h) * u n) -> forall n, u n <= u 0 * Qpow (1 + alpha * h) n (ProcessGronwallInequality.v:115) — от рекуррентной оценки произвольной последовательности к геометрической оценке. ' + CL + '.';
const N_FORC = 'gronwall_inequality_forced : forall alpha beta h (u : nat -> Q), 0 < alpha -> 0 <= h -> (forall n, u (S n) <= (1 + alpha * h) * u n + beta * h) -> forall n, u n <= (u 0 + beta / alpha) * Qpow (1 + alpha * h) n - beta / alpha (ProcessGronwallInequality.v:150); посылки здесь сильнее: 0 < alpha и 0 <= h. Явный вид итерации — gronwall_iterate_closed (:131); при alpha = 0 приток накапливается линейно — gronwall_iterate_alpha_zero (:141). ' + CL + '.';
const N_EBG = 'euler_bound_is_gronwall_iterate : forall L h d n, qpow (1 + L * h) n * d == gronwall_iterate L 0 h d n (ProcessGronwallInequality.v:197) — правая часть euler_diff_bound есть однородная итерация Гронуолла с alpha = L, u0 = d. Две степенные функции, qpow (ProcessExpProcess.v:36) и Qpow (SeriesConvergence.v:35), совпадают — qpow_is_Qpow (:189). ' + CL + '.';
const N_EDG = 'euler_divergence_gronwall : forall y0 z0 n, Qabs (euler f h y0 n - euler f h z0 n) <= gronwall_iterate L 0 h (Qabs (y0 - z0)) n (ProcessGronwallInequality.v:227); доказательство — применение gronwall_inequality_from (:90) к последовательности |Δ_n| с шагом euler_step_diff (ProcessODEStability.v:64). ' + PREM + ' В записи страницы — euler_divergence_gronwall_Qpow (:243). ' + CL + '.';
const N_SAME = 'euler_same_start : forall y0 z0 n, y0 == z0 -> euler f h y0 n == euler f h z0 n (ProcessGronwallInequality.v:255) — следствие оценки расхождения при нулевом возмущении. ' + PREM + ' ' + CL + '.';
const N_PFS = 'picard_fixed_stability : forall y0 z0 N (y z : nat -> Q), (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) -> (forall k, (k <= N)%nat -> picard_op f h z0 z k == z k) -> forall k, (k <= N)%nat -> Qabs (y k - z k) <= qpow (1 + L * h) k * Qabs (y0 - z0) (ProcessGronwallInequality.v:284). Опора — picard_fixed_eq_euler (ProcessPicardGridSolution.v:366): неподвижная точка сеточного оператора Пикара есть ломаная Эйлера; ломаная неподвижна — euler_is_picard_fixed (:274). Условия L·T < 1 нет. ' + CL + '.';
const N_PUZ = 'picard_unique_as_zero_perturbation : forall y0 z0 N (y z : nat -> Q), y0 == z0 -> (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) -> (forall k, (k <= N)%nat -> picard_op f h z0 z k == z k) -> forall k, (k <= N)%nat -> y k == z k (ProcessGronwallInequality.v:299) — единственность получена из picard_fixed_stability (:284) при нулевом возмущении. ' + CL + '.';
const N_PUAR = 'picard_unique_any_rate : forall (f : Q -> Q -> Q) (L : Q), (forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2)) -> forall (h y0 : Q) (N : nat) (y z : nat -> Q), (forall k, (k <= N)%nat -> picard_op f h y0 y k == y k) -> (forall k, (k <= N)%nat -> picard_op f h y0 z k == z k) -> forall k, (k <= N)%nat -> y k == z k (ProcessPicardGridSolution.v:330); посылки L * Tlen < 1 нет. ' + CL + '.';
const N_PU = 'picard_unique (ProcessPicardOperator.v:183): при 0 < L, липшицевости f, 0 <= h и L * Tlen < 1 (посылка раздела Hrate, :181) две функции, неподвижные под picard_op в узлах k <= N, совпадают в этих узлах; доказательство через конечный максимум gmax (:156). ' + CL + '.';
const N_ECD = 'euler_continuous_dependence : forall n eps, 0 < eps -> exists delta, 0 < delta ' + AND + ' forall y0 z0, Qabs (y0 - z0) < delta -> Qabs (euler f h y0 n - euler f h z0 n) < eps (ProcessGronwallInequality.v:319) — при данном шаге h и данном числе шагов n. ' + PREM + ' ' + CL + '.';
const N_ECU = 'euler_continuous_dependence_uniform : forall f L, 0 <= L -> (липшицевость f по y) -> forall t, 0 <= t -> forall eps, 0 < eps -> exists delta, 0 < delta ' + AND + ' forall (k : nat) (y0 z0 : Q), Qabs (y0 - z0) < delta -> Qabs (euler f (t / inject_Z (Z.of_nat (S k))) y0 (S k) - euler f (t / inject_Z (Z.of_nat (S k))) z0 (S k)) < eps (ProcessGronwallInequality.v:467) — delta выбирается до числа шагов k: одно для всех сеток, приводящих в момент t. ' + CL + '.';
const N_SHARP = 'euler_diff_bound_sharp : forall L h y0 z0 n, 0 <= L -> 0 <= h -> Qabs (euler (fun _ y => L * y) h y0 n - euler (fun _ y => L * y) h z0 n) == qpow (1 + L * h) n * Qabs (y0 - z0) (ProcessGronwallInequality.v:360) — для правой части L·y в оценке стоит равенство; липшицевость этой правой части — linear_is_lipschitz (:351). ' + CL + '.';
const N_EXPT = 'euler_divergence_expt : forall f L, 0 <= L -> (липшицевость f по y) -> forall t, 0 <= t -> forall (k : nat) (y0 z0 : Q), Qabs (euler f (t / inject_Z (Z.of_nat (S k))) y0 (S k) - euler f (t / inject_Z (Z.of_nat (S k))) z0 (S k)) <= expt_process (L * t) k * Qabs (y0 - z0) (ProcessGronwallInequality.v:381) — подстановка шага h = t/(k+1) в оценку расхождения: за k+1 шагов, то есть в момент t. ' + CL + '.';
const N_UNI = 'euler_divergence_uniform : те же посылки и forall k0 : nat, L * t < inject_Z (Z.of_nat (S k0)) -> forall (k : nat) (y0 z0 : Q), Qabs (...) <= 1 / qpow (1 - L * t / inject_Z (Z.of_nat (S k0))) (S k0) * Qabs (y0 - z0) (ProcessGronwallInequality.v:405) — правая часть от числа шагов k не зависит. При L·t < 1 — euler_divergence_expt_small (:423): не больше |y0 − z0| / (1 − L·t). ' + CL + '.';
const N_MONO = 'expt_monotone : forall s k, 0 <= s -> expt_process s k <= expt_process s (S k) (ProcessExpLadder.v:396). ' + CL + '.';
const N_BND = 'expt_bounded : forall s m k0, 0 <= s -> s < inject_Z (Z.of_nat (S k0)) -> expt_process s m <= 1 / qpow (1 - s / inject_Z (Z.of_nat (S k0))) (S k0) (ProcessExpLadder.v:519) — потолок рационален и от номера стадии m не зависит. ' + CL + '.';
const N_CAU = 'expt_process_is_Cauchy : forall s, 0 <= s -> is_Cauchy (expt_process s) (ProcessExpLadder.v:565); is_Cauchy (ProcessCore.v:68): для всякого eps > 0 найдётся N, за которым стадии отличаются меньше чем на eps. При s = L·t — growth_factor_is_Cauchy (ProcessGronwallInequality.v:502). ' + CL + '.';
const N_MOD = 'expt_modulus : forall s k0, 0 <= s -> s < inject_Z (Z.of_nat (S k0)) -> forall m n, (k0 <= n)%nat -> expt_process s m - expt_process s n <= 1 / qpow (1 - s / inject_Z (Z.of_nat (S k0))) (S k0) * (s * s / inject_Z (Z.of_nat (S n))) (ProcessExpLadder.v:538) — явный модуль: зазор не больше B·s²/(n+1). ' + CL + '.';
const N_ONE = 'expt_at_one : forall k, expt_process 1 k = exp1_process k (ProcessExpLadder.v:347); exp1_process (ProcessExpProcess.v:47) — процесс (1 + 1/n)^n Глав 8.2 и 8.5. ' + CL + '.';
const N_EGE = 'euler_growth_is_expt_process : qpow (1 + s / inject_Z (Z.of_nat (S k))) (S k) == expt_process s k (ProcessODEStability.v:110) — развёрнутое определение expt_process (ProcessExpProcess.v:51); доказательство — unfold expt_process; reflexivity. ' + CL + '.';
const N_NEED = 'decay_factor_needs_u0_nonneg : ~ (forall r u0 n, 0 <= r -> r <= 1 -> u0 * Qpow r n <= u0) (ProcessGronwallInequality.v:513) — свидетель: u0 = −1, r = 1/2, n = 1. ' + CL + '.';
const N_GDF = 'gronwall_decay_factor : 0 <= r -> r <= 1 -> 0 <= u0 -> u0 * Qpow r n <= u0 (ProcessGronwall.v:112) — три посылки; утверждение о числе u0·r^n. ' + CL + '.';
const N_DEC = 'gronwall_iterate_decay : forall alpha h u0 n, 0 <= 1 + alpha * h -> 1 + alpha * h <= 1 -> 0 <= u0 -> gronwall_iterate alpha 0 h u0 n <= u0 (ProcessGronwallInequality.v:523) — о самой итерации. ' + CL + '.';
const N_DECM = 'gronwall_iterate_decay_monotone : forall alpha h u0 n, 0 <= 1 + alpha * h -> 1 + alpha * h <= 1 -> 0 <= u0 -> gronwall_iterate alpha 0 h u0 (S n) <= gronwall_iterate alpha 0 h u0 n (ProcessGronwallInequality.v:544); неотрицательность итерации — gronwall_iterate_hom_nonneg (:531). ' + CL + '.';
const N_ABS = 'gronwall_iterate_abs : forall alpha h u0 n, Qabs (gronwall_iterate alpha 0 h u0 n) == Qabs u0 * Qpow (Qabs (1 + alpha * h)) n (ProcessGronwallInequality.v:558). ' + CL + '.';
const N_ABSD = 'gronwall_iterate_abs_decay : forall alpha h u0 n, Qabs (1 + alpha * h) <= 1 -> Qabs (gronwall_iterate alpha 0 h u0 n) <= Qabs u0 (ProcessGronwallInequality.v:570) — начало любого знака. ' + CL + '.';
const N_ABSM = 'gronwall_iterate_abs_monotone : forall alpha h u0 n, Qabs (1 + alpha * h) <= 1 -> Qabs (gronwall_iterate alpha 0 h u0 (S n)) <= Qabs (gronwall_iterate alpha 0 h u0 n) (ProcessGronwallInequality.v:578). ' + CL + '.';
const N_VAN = 'gronwall_iterate_vanishes : forall alpha h u0, Qabs (1 + alpha * h) < 1 -> forall eps, 0 < eps -> exists N : nat, forall n, (N <= n)%nat -> Qabs (gronwall_iterate alpha 0 h u0 n) < eps (ProcessGronwallInequality.v:596); опора — Qpow_vanish (SeriesConvergence.v:164). ' + CL + '.';
const NOEXP = 'Числа e^{Lt} как завершённого объекта, равенства потолка этому числу и оценки расхождения при неограниченном числе шагов с постоянной, не зависящей от n, в ProcessGronwallInequality.v и ProcessExpLadder.v нет (шапки файлов, раздел «NOT claimed»).';
const ALL38 = 'все 38 объявлений ProcessGronwallInequality.v: Closed under the global context';
const ALL44 = 'все 44 утверждения ProcessExpLadder.v: Closed under the global context';

// --- цитаты страницы после правок
const C9 = 'Глава 8.3 дала гарантию: при липшицевости правой части на достаточно коротком отрезке ($LT<1$) оператор Пикара сжимает, и его итерации сближаются геометрически; а на сетке решение существует и единственно при любой длине отрезка.';
const C33 = L('без аксиом доказана и $¤varepsilon$-сходимость множителя — свойство Коши лестницы $(1+Lt/n)^n$; завершённый $e^{Lt}$ как объект формальный слой не строит.');
const C40 = L('Множитель $(1+Lh)^n$ — рациональный процесс; его предел $e^{Lt}$ — роль-предел, а $¤varepsilon$-сходимость есть свойство Коши самого процесса и аксиом не требует.');
const C139 = L('А если множитель не превосходит единицы ($r = 1+¤alpha h$ в диапазоне $0 ¤le r ¤le 1$ — затухающий режим), итерация с неотрицательным началом $u_0 ¤ge 0$ не растёт, а *убывает*: $u_{n+1} ¤le u_n ¤le u_0$.[^7]');
const C146 = L('устойчивость и затухание — два его режима ($¤alpha$ положительно — или отрицательно при $¤lvert¤alpha¤rvert h ¤le 1$.)');
const C158 = 'Если взять шаг $h = t/n$ (то есть достичь момента $t$ за $n$ шагов), множитель станет $(1 + L t/n)^n$ — а это в точности стадия процесса для $e^{Lt}$, того самого $e$-процесса, что разбирался в Главе 8.2 и разбирается в Главе 8.5.[^8]';
const C164 = L('Доказано конкретное и процессное: пошаговая и геометрическая оценки расхождения, их совпадение с однородным Гронуоллом, тождество множителя со стадией $e^{Lt}$-процесса, оценка расхождения в момент $t$ числом, не зависящим от числа шагов, и $¤varepsilon$-сходимость самой лестницы множителей.');
const C167 = 'Завершённый $e^{Lt}$ и безусловная оценка на бесконечном интервале — роль-предел и граница: в формальном слое их нет.';
const C191 = 'Венчает — тождество множителя $(1+Lt/n)^n$ со стадией $e^{Lt}$-процесса и оценка расхождения в момент $t$ этой стадией: лестница стадий не убывает, ограничена и образует процесс Коши.';
const C193 = L('Универсальный слой L3 в доказанное не входит: ни рациональные оценки, ни $¤varepsilon$-сходимость множителя его не требуют; к L3 относится лишь актуализация $e^{Lt}$ как завершённого объекта (Глава 8.1, § «Где появляется граница»), и в формальном слое её нет.');
const F1G = L('`ProcessGronwall.v` (`gronwall_step`, `gronwall_iterate`, `gronwall_beta_zero`: $u_0(1+¤alpha h)^n$; `gronwall_decay_factor`: затухание при множителе $¤le 1$)');
const F1N = 'а также `ProcessGronwallInequality.v` (неравенство Гронуолла для произвольной последовательности, оценка расхождения как его случай, оценки в момент $t$, затухание; 0 аксиом)';
const F1L = '`ProcessExpLadder.v` (лестница $(1+s/n)^n$: рост, ограниченность, свойство Коши; 0 аксиом)';
const F2A = '`picard_unique` в `ProcessPicardOperator.v`: при $LT<1$, если две грид-функции неподвижны под оператором Пикара, они совпадают во всех узлах сетки; без условия на $LT$ — `picard_unique_any_rate` (`ProcessPicardGridSolution.v`).';
const F2B = L('Прочтение «единственность есть устойчивость при нулевом возмущении» записано теоремами в `ProcessGronwallInequality.v`: две неподвижные точки с началами $y_0$ и $¤tilde y_0$ расходятся в узле $k$ не более чем в $(1+Lh)^k$ раз от $¤lvert y_0 - ¤tilde y_0¤rvert$ (`picard_fixed_stability`), при равных началах они совпадают (`picard_unique_as_zero_perturbation`); для самих ломаных Эйлера — `euler_same_start`. 0 аксиом (Глава 8.3).');
const F4B = 'Оценка точна: для $f(t,y) = Ly$ в ней стоит равенство (`euler_diff_bound_sharp`).';
const F4C = L('«Малое возмущение даёт малое расхождение» в форме «для всякого $¤varepsilon$ найдётся $¤delta$» — `euler_continuous_dependence` (на данном шаге) и `euler_continuous_dependence_uniform` (в момент $t$: одно $¤delta$ для всякого числа шагов) в `ProcessGronwallInequality.v`. 0 аксиом.');
const F6B = L('При $¤alpha=L$ это правая часть `euler_diff_bound` (`euler_bound_is_gronwall_iterate`).');
const F6C = L('Само неравенство — для всякой последовательности, растущей не быстрее шага, при неотрицательном множителе $1+¤alpha h$ — `gronwall_inequality` (однородный случай — `gronwall_inequality_hom`, с притоком в явном виде — `gronwall_inequality_forced`); оценка расхождения как его случай — `euler_divergence_gronwall`. Все — в `ProcessGronwallInequality.v`, 0 аксиом.');
const F7A = L('`gronwall_decay_factor` в `ProcessGronwall.v`: для $0 ¤le r ¤le 1$ и $u_0 ¤ge 0$ выполнено $u_0 r^n ¤le u_0$; без условия $u_0 ¤ge 0$ это неверно (`decay_factor_needs_u0_nonneg`).');
const F7B = L('Для самой итерации — `gronwall_iterate_decay` ($u_n ¤le u_0$) и `gronwall_iterate_decay_monotone` ($u_{n+1} ¤le u_n$) в `ProcessGronwallInequality.v`.');
const F7C = L('При начале любого знака убывает модуль: если $¤lvert r¤rvert ¤le 1$, то $¤lvert u_{n+1}¤rvert ¤le ¤lvert u_n¤rvert ¤le ¤lvert u_0¤rvert$ (`gronwall_iterate_abs_monotone`, `gronwall_iterate_abs_decay`), а при $¤lvert r¤rvert < 1$ итерация стремится к нулю (`gronwall_iterate_vanishes`). 0 аксиом.');
const F8A = L('`euler_growth_is_expt_process` в `ProcessODEStability.v`: множитель $(1+s/(k{+}1))^{k+1}$ *есть* стадия $¤texttt{expt¤_process} s k$ из `ProcessExpProcess.v` — по определению этого процесса. 0 аксиом.');
const F8B = L('Содержание тождеству дают теоремы: подстановка шага $h = t/n$ в оценку расхождения — `euler_divergence_expt` (`ProcessGronwallInequality.v`): расхождение в момент $t$ не больше стадии лестницы, умноженной на $¤lvert¤Delta_0¤rvert$;');
const F8C = 'стадии не убывают (`expt_monotone`) и ограничены числом, одним для всех (`expt_bounded`; оба — `ProcessExpLadder.v`), так что расхождение в момент $t$ оценено независимо от числа шагов (`euler_divergence_uniform`);';
const F8D = 'лестница множителей — процесс Коши с явным модулем (`expt_process_is_Cauchy`, `expt_modulus`); при $s = 1$ она совпадает с $e$-процессом (`expt_at_one`). 0 аксиом.';

{
  const { fix, add, save, claimOf } = open('part08-ch04');

  // ------------------------------------------------------------ вводная часть (место 4.5)
  fix('Глава 8.3 дала гарантию: при липшицевости правой части', 'picard_op_contraction', { claim: C9, assumptions: CL,
    note: DONE + ': в пересказе Главы 8.3 названо условие сжатия. picard_op_contraction (ProcessPicardOperator.v:102): |Φy_k − Φz_k| <= (L·T)·D на узлах k <= N; сжатием оценка становится при L * Tlen < 1 (посылка Hrate, :181). «Итерации сближаются геометрически» — picard_iter_gap (:234). «На сетке решение существует и единственно при любой длине отрезка» — picard_fixed_exists (ProcessPicardGridSolution.v:243), picard_unique_any_rate (:330); шаг 2 Части VIII. ' + CL + '.' });
  add({ theorem: 'picard_fixed_exists', file: GS, assumptions: CL, claim: C9,
    note: '«На сетке решение существует при любой длине отрезка»: picard_fixed_exists : forall N, exists y : nat -> Q, forall k, (k <= N)%nat -> picard_op f h y0 y k == y k (ProcessPicardGridSolution.v:243); условия на L·T нет. ' + CL + '.' });
  add({ theorem: 'picard_unique_any_rate', file: GS, assumptions: CL, claim: C9, note: '«И единственно при любой длине отрезка»: ' + N_PUAR });

  // ------------------------------------------------------------ «Что эта глава утверждает» (место 4.3)
  fix(L('переход к $¤varepsilon$-сходимости множителя к завершённому'), null, { theorem: 'expt_process_is_Cauchy', file: EL, claim: C33, assumptions: CL, page_price: 'без аксиом',
    note: DONE + ': слова «относится к L3-слою» сняты — цена названа по компилятору. ' + N_CAU + ' ' + NOEXP });
  fix('Множитель $(1+Lh)^n$ — рациональный процесс', null, { theorem: 'expt_process_is_Cauchy', file: EL, claim: C40, assumptions: CL, page_price: 'аксиом не требует',
    note: DONE + ': слова «наследует L3» сняты. ' + N_CAU + ' Явный модуль — expt_modulus (ProcessExpLadder.v:538).' });

  // ------------------------------------------------------------ каркас (места 4.1, 4.2)
  fix('неравенство Гронуолла обобщает', 'gronwall_beta_zero', { theorem: 'gronwall_inequality_hom', file: GI, assumptions: CL,
    note: KEPT + '«рост, ограниченный кратным себя, влечёт геометрическую оценку» теперь теорема для произвольной последовательности. ' + N_HOM + ' С притоком — ' + N_GI + ' Прежняя опора gronwall_beta_zero (ProcessGronwall.v:80) — явный вид последовательности, заданной равенством.' });
  fix('множитель $(1+Lh)^n$ есть стадия процесса для', 'euler_growth_is_expt_process', { assumptions: CL,
    note: N_EGE + ' Содержание тождеству дают теоремы шага 4 Части VIII: оценка расхождения в момент t стадией лестницы (euler_divergence_expt, ProcessGronwallInequality.v:381), рост, ограниченность и свойство Коши лестницы (ProcessExpLadder.v) — сноска 8.' });

  // ------------------------------------------------------------ «Единственность как нулевое возмущение»
  fix('*единственность есть устойчивость при нулевом возмущении*', 'euler_diff_bound', { theorem: 'euler_same_start', file: GI, assumptions: CL,
    note: KEPT + 'прочтение записано теоремами. ' + N_SAME + ' Для неподвижных точек оператора Пикара — picard_fixed_stability (:284) и picard_unique_as_zero_perturbation (:299); сноска 2.' });
  add({ theorem: 'picard_fixed_stability', file: GI, assumptions: CL, claim: claimOf('*единственность есть устойчивость при нулевом возмущении*'),
    note: 'Связь двух предметов — неподвижных точек сеточного оператора Пикара (о них picard_unique) и ломаных Эйлера (о них оценка расхождения): ' + N_PFS });

  // ------------------------------------------------------------ «Расхождение траекторий»
  fix('Расхождение в любой момент ограничено начальным возмущением', 'euler_diff_bound', { assumptions: CL,
    note: 'euler_diff_bound (ProcessODEStability.v:86): при всяком n. ' + CL + '. Оценка точна: ' + N_SHARP });
  fix('На *конечном* интервале множитель конечен', 'euler_diff_bound', { theorem: 'euler_continuous_dependence', file: GI, assumptions: CL,
    note: KEPT + '«малое возмущение даёт малое расхождение» записано в форме «для всякого eps найдётся delta». ' + N_ECD + ' В момент t, с одним delta для всякого числа шагов, — euler_continuous_dependence_uniform (:467). Опора обеих — euler_diff_bound (ProcessODEStability.v:86).' });
  add({ theorem: 'euler_continuous_dependence_uniform', file: GI, assumptions: CL, claim: claimOf('На *конечном* интервале множитель конечен'),
    note: '«На конечном интервале множитель конечен» — в момент t множитель ограничен числом, не зависящим от сетки: ' + N_ECU + ' Опора — ' + N_UNI });

  // ------------------------------------------------------------ «Неравенство Гронуолла» (места 4.1, 4.4)
  fix('Это и есть процессная форма Гронуолла', 'gronwall_beta_zero', { assumptions: CL,
    note: KEPT + '«это» — явный вид однородной итерации: gronwall_beta_zero (ProcessGronwall.v:80). «Совпадает с оценкой расхождения» — euler_bound_is_gronwall_iterate (ProcessGronwallInequality.v:197); «устойчивость есть Гронуолл для расхождения» — euler_divergence_gronwall (:227). Само неравенство — gronwall_inequality (:104); сноска 6. ' + CL + '.' });
  add({ theorem: 'euler_bound_is_gronwall_iterate', file: GI, assumptions: CL, claim: claimOf('Это и есть процессная форма Гронуолла'),
    note: L('«При $¤alpha = L$, $u_0 = ¤lvert¤Delta_0¤rvert$ она совпадает с оценкой расхождения»: ') + N_EBG });
  add({ theorem: 'euler_divergence_gronwall', file: GI, assumptions: CL, claim: claimOf('Это и есть процессная форма Гронуолла'),
    note: '«Устойчивость есть Гронуолл для расхождения»: ' + N_EDG });
  fix('А если множитель не превосходит единицы', 'gronwall_decay_factor', { theorem: 'gronwall_iterate_decay_monotone', file: GI, claim: C139, assumptions: CL,
    note: DONE + ': названо условие u0 >= 0, оценка записана шаг за шагом. ' + N_DECM + ' Без условия на начало формула неверна — decay_factor_needs_u0_nonneg (:513).' });
  add({ theorem: 'gronwall_iterate_decay', file: GI, assumptions: CL, claim: C139, note: L('«$u_n ¤le u_0$» для самой итерации: ') + N_DEC });
  add({ theorem: 'gronwall_iterate_decay', file: GI, assumptions: CL, claim: C146,
    note: DONE + ' (вопрос 2 шага 4, вариант 1): курсив уточнён условием. При alpha < 0, h >= 0 и |alpha|·h <= 1 множитель 1 + alpha·h лежит в [0, 1] — посылки затухания: ' + N_DEC + ' По модулю затухание держится до |1 + alpha·h| <= 1 (gronwall_iterate_abs_decay, :570); при |1 + alpha·h| > 1 модуль растёт: ' + N_ABS });

  // ------------------------------------------------------------ «Множитель роста и e^{Lt}» (места 4.1–4.3)
  fix('Если взять шаг $h = t/n$', 'euler_growth_is_expt_process', { claim: C158, assumptions: CL,
    note: DONE + ' (вопрос 3 шага 4, вариант 1): «разбирался в Главах 8.2 и 8.5» → «разбирался в Главе 8.2 и разбирается в Главе 8.5». ' + N_EGE + ' Подстановка h = t/n в оценку расхождения — euler_divergence_expt (ProcessGronwallInequality.v:381); «того самого e-процесса» — expt_at_one (ProcessExpLadder.v:347). Сноска 8.' });
  add({ theorem: 'euler_divergence_expt', file: GI, assumptions: CL, claim: C158, note: '«Множитель станет (1 + Lt/n)^n» — подстановка шага теоремой: ' + N_EXPT });
  add({ theorem: 'expt_at_one', file: EL, assumptions: CL, claim: C158, note: '«Того самого e-процесса»: ' + N_ONE });
  fix('Доказано конкретное и процессное', null, { theorem: 'euler_divergence_uniform', file: GI, claim: C164, assumptions: CL,
    note: DONE + ': перечень доказанного приведён к теоремам. Пошаговая и геометрическая оценки — euler_step_diff, euler_diff_bound (ProcessODEStability.v:64, :86); совпадение с однородным Гронуоллом — euler_bound_is_gronwall_iterate (ProcessGronwallInequality.v:197); тождество множителя со стадией — euler_growth_is_expt_process (ProcessODEStability.v:110), по определению; оценка в момент t числом, не зависящим от числа шагов: ' + N_UNI + ' ε-сходимость лестницы — expt_process_is_Cauchy (ProcessExpLadder.v:565).' });
  add({ theorem: 'euler_bound_is_gronwall_iterate', file: GI, assumptions: CL, claim: C164, note: '«Их совпадение с однородным Гронуоллом»: ' + N_EBG });
  add({ theorem: 'expt_process_is_Cauchy', file: EL, assumptions: CL, claim: C164, note: L('«$¤varepsilon$-сходимость самой лестницы множителей»: ') + N_CAU });
  fix(L('$¤varepsilon$-сходимость множителя к завершённому'), null, { claim: C167, file: GI, page_price: '',
    note: DONE + ': цена «L3» со страницы снята. Статус честный. ' + NOEXP });

  // ------------------------------------------------------------ разбор, Rules (места 4.1–4.3; вопрос 1)
  fix('Над ней — геометрическая оценка', 'gronwall_beta_zero', { assumptions: CL,
    note: KEPT + 'геометрическая оценка — euler_diff_bound (ProcessODEStability.v:86). Формула в скобках — gronwall_beta_zero (ProcessGronwall.v:80). «Её обобщение — неравенство Гронуолла» теперь теорема: gronwall_inequality (ProcessGronwallInequality.v:104), оценка расхождения получена её применением (euler_divergence_gronwall, :227). «Затухание при множителе <= 1» — gronwall_iterate_decay (:523), при u0 >= 0. ' + CL + '.' });
  add({ theorem: 'gronwall_inequality', file: GI, assumptions: CL, claim: claimOf('Над ней — геометрическая оценка'), note: '«И её обобщение — неравенство Гронуолла»: ' + N_GI });
  add({ theorem: 'gronwall_iterate_decay', file: GI, assumptions: CL, claim: claimOf('Над ней — геометрическая оценка'), note: L('«Затухание при множителе $¤le 1$»: ') + N_DEC });
  fix('Венчает — тождество множителя', 'euler_growth_is_expt_process', { claim: C191, assumptions: CL,
    note: DONE + ': к тождеству добавлено то, что даёт ему содержание. ' + N_EGE + ' Оценка расхождения в момент t стадией — euler_divergence_expt (ProcessGronwallInequality.v:381); лестница не убывает (expt_monotone, ProcessExpLadder.v:396), ограничена (expt_bounded, :519), процесс Коши (expt_process_is_Cauchy, :565).' });
  add({ theorem: 'euler_divergence_expt', file: GI, assumptions: CL, claim: C191, note: '«Оценка расхождения в момент t этой стадией»: ' + N_EXPT });
  add({ theorem: 'expt_monotone', file: EL, assumptions: CL, claim: C191, note: '«Лестница стадий не убывает»: ' + N_MONO });
  add({ theorem: 'expt_bounded', file: EL, assumptions: CL, claim: C191, note: '«Ограничена»: ' + N_BND });
  add({ theorem: 'expt_process_is_Cauchy', file: EL, assumptions: CL, claim: C191, note: '«И образует процесс Коши»: ' + N_CAU });
  fix('Универсальный слой включает L3', null, { claim: C193, file: GI, page_price: 'L3 в доказанное не входит', assumptions: ALL38 + '; ' + ALL44,
    note: DONE + ' (вопрос 1 шага 4, вариант 1): слово об L3 оставлено один раз и отнесено к тезису автора — Глава 8.1, § «Где появляется граница» («актуализация как готовой функции — уже не конструкция, а постулат L3»). По компилятору: рациональные оценки и свойство Коши лестницы множителей — без допущений (ProcessODEStability.v, ProcessGronwall.v, ProcessGronwallInequality.v, ProcessExpLadder.v). ' + NOEXP });

  // ------------------------------------------------------------ таблица и «Что даёт разбор»
  fix(L('| $¤lvert¤Delta_{n+1}¤rvert¤le(1+Lh)¤lvert¤Delta_n¤rvert$; Гронуолл'), 'euler_step_diff', {
    note: 'Строка таблицы повторяет три формулы: euler_step_diff (ProcessODEStability.v:64), gronwall_beta_zero (ProcessGronwall.v:80), euler_growth_is_expt_process (ProcessODEStability.v:110). С шага 4 Части VIII за словом «Гронуолл» стоит неравенство для произвольной последовательности (gronwall_inequality, ProcessGronwallInequality.v:104), за словами «множитель = стадия» — оценка расхождения стадией (euler_divergence_expt, :381).' });
  fix('Единственность вписывается как предельный случай', 'gronwall_beta_zero', { theorem: 'euler_divergence_gronwall', file: GI, assumptions: CL,
    note: KEPT + '«Гронуолл — общее Правило, частным случаем которого служит оценка расхождения» теперь теорема: ' + N_EDG + ' «Единственность как предельный случай (нулевое возмущение)» — picard_unique_as_zero_perturbation (:299), euler_same_start (:255).' });
  add({ theorem: 'picard_unique_as_zero_perturbation', file: GI, assumptions: CL, claim: claimOf('Единственность вписывается как предельный случай'),
    note: '«Единственность вписывается как предельный случай (нулевое возмущение)»: ' + N_PUZ });
  add({ theorem: 'gronwall_inequality', file: GI, assumptions: CL, claim: claimOf('Единственность вписывается как предельный случай'), note: '«Гронуолл — общее Правило»: ' + N_GI });

  // ------------------------------------------------------------ сноска 1
  fix('`ProcessGronwall.v` (`gronwall_step`', null, { claim: F1G });
  add({ theorem: null, file: GI, claim: F1N, page_price: '0 аксиом', assumptions: ALL38,
    note: DONE + ': новый опорный файл в сноске. ProcessGronwallInequality.v: 37 Qed и одно определение (gronwall_cex); строк Axiom, Parameter, Admitted нет. Неравенство для произвольной последовательности — gronwall_inequality (:104); оценка расхождения как его случай — euler_divergence_gronwall (:227); оценки в момент t — euler_divergence_expt (:381), euler_divergence_uniform (:405); затухание — gronwall_iterate_decay (:523), gronwall_iterate_vanishes (:596).' });
  add({ theorem: null, file: EL, claim: F1L, page_price: '0 аксиом', assumptions: ALL44,
    note: DONE + ': новый опорный файл в сноске (шаг 1 Части VIII). ProcessExpLadder.v: 44 Qed; строк Axiom, Parameter, Admitted нет. Рост — expt_monotone (:396); ограниченность — expt_bounded (:519); свойство Коши — expt_process_is_Cauchy (:565).' });

  // ------------------------------------------------------------ сноска 2 (место 4.5)
  fix('`picard_unique` в `ProcessPicardOperator.v`', 'picard_unique', { claim: F2A, assumptions: CL, page_price: '0 аксиом',
    note: DONE + ': названо условие LT < 1. ' + N_PU + ' Без условия — picard_unique_any_rate (ProcessPicardGridSolution.v:330).' });
  add({ theorem: 'picard_unique_any_rate', file: GS, assumptions: CL, claim: F2A, page_price: '0 аксиом', note: DONE + ': новое имя в сноске. ' + N_PUAR });
  add({ theorem: 'picard_fixed_stability', file: GI, assumptions: CL, claim: F2B, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_PFS });
  add({ theorem: 'picard_unique_as_zero_perturbation', file: GI, assumptions: CL, claim: F2B, page_price: '0 аксиом', note: N_PUZ });
  add({ theorem: 'euler_same_start', file: GI, assumptions: CL, claim: F2B, page_price: '0 аксиом', note: N_SAME });

  // ------------------------------------------------------------ сноска 4
  add({ theorem: 'euler_diff_bound_sharp', file: GI, assumptions: CL, claim: F4B, note: DONE + ': новая фраза. ' + N_SHARP });
  add({ theorem: 'euler_continuous_dependence', file: GI, assumptions: CL, claim: F4C, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_ECD });
  add({ theorem: 'euler_continuous_dependence_uniform', file: GI, assumptions: CL, claim: F4C, page_price: '0 аксиом', note: N_ECU });

  // ------------------------------------------------------------ сноска 6 (место 4.1)
  fix(L('При $¤alpha=L$ это правая часть'), 'euler_diff_bound', { claim: F6B, assumptions: CL,
    note: DONE + ': совпадение названо теоремой. Правая часть euler_diff_bound (ProcessODEStability.v:86) — qpow (1 + L * h) n * Qabs (y0 - z0). ' + N_EBG });
  add({ theorem: 'euler_bound_is_gronwall_iterate', file: GI, assumptions: CL, claim: F6B, note: DONE + ': новое имя в сноске. ' + N_EBG });
  add({ theorem: 'gronwall_inequality', file: GI, assumptions: CL, claim: F6C, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_GI });
  add({ theorem: 'gronwall_inequality_hom', file: GI, assumptions: CL, claim: F6C, page_price: '0 аксиом', note: N_HOM });
  add({ theorem: 'gronwall_inequality_forced', file: GI, assumptions: CL, claim: F6C, page_price: '0 аксиом', note: N_FORC });
  add({ theorem: 'euler_divergence_gronwall', file: GI, assumptions: CL, claim: F6C, page_price: '0 аксиом', note: N_EDG });

  // ------------------------------------------------------------ сноска 7 (место 4.4)
  fix('`gronwall_decay_factor` в `ProcessGronwall.v`', 'gronwall_decay_factor', { claim: F7A, assumptions: CL, page_price: '0 аксиом',
    note: DONE + ': названа третья посылка. ' + N_GDF });
  add({ theorem: 'decay_factor_needs_u0_nonneg', file: GI, assumptions: CL, claim: F7A, page_price: '0 аксиом', note: DONE + ': новое имя в сноске. ' + N_NEED });
  add({ theorem: 'gronwall_iterate_decay', file: GI, assumptions: CL, claim: F7B, note: DONE + ': новая фраза. ' + N_DEC });
  add({ theorem: 'gronwall_iterate_decay_monotone', file: GI, assumptions: CL, claim: F7B, note: N_DECM });
  add({ theorem: 'gronwall_iterate_abs_monotone', file: GI, assumptions: CL, claim: F7C, page_price: '0 аксиом', note: DONE + ': новая фраза; r на странице — множитель 1 + alpha·h. ' + N_ABSM });
  add({ theorem: 'gronwall_iterate_abs_decay', file: GI, assumptions: CL, claim: F7C, page_price: '0 аксиом', note: N_ABSD + ' Равенство для модуля: ' + N_ABS });
  add({ theorem: 'gronwall_iterate_vanishes', file: GI, assumptions: CL, claim: F7C, page_price: '0 аксиом', note: N_VAN });

  // ------------------------------------------------------------ сноска 8 (места 4.2, 4.3)
  fix('`euler_growth_is_expt_process` в `ProcessODEStability.v`', 'euler_growth_is_expt_process', { claim: F8A, assumptions: CL, page_price: '0 аксиом',
    note: DONE + ': статус тождества назван («по определению этого процесса»); слово «батч C» снято. ' + N_EGE });
  add({ theorem: 'euler_divergence_expt', file: GI, assumptions: CL, claim: F8B, note: DONE + ': новая фраза. n на странице — число шагов k + 1. ' + N_EXPT });
  add({ theorem: 'expt_monotone', file: EL, assumptions: CL, claim: F8C, note: DONE + ': новая фраза. ' + N_MONO });
  add({ theorem: 'expt_bounded', file: EL, assumptions: CL, claim: F8C, note: N_BND });
  add({ theorem: 'euler_divergence_uniform', file: GI, assumptions: CL, claim: F8C, note: N_UNI });
  add({ theorem: 'expt_process_is_Cauchy', file: EL, assumptions: CL, claim: F8D, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_CAU });
  add({ theorem: 'expt_modulus', file: EL, assumptions: CL, claim: F8D, page_price: '0 аксиом', note: N_MOD });
  add({ theorem: 'expt_at_one', file: EL, assumptions: CL, claim: F8D, page_price: '0 аксиом', note: N_ONE });

  save();
}
