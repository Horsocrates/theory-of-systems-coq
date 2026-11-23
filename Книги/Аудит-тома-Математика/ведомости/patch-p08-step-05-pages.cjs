// Часть VIII, шаг 5, страницы (2026-11-23, слово автора «Делай»): 19 правок главы VIII.5 внесены
// (советуемые варианты трёх вопросов: знак в решении осциллятора исправлен; фраза о законе энергии добавлена
// в основной текст; абзац о проверке устойчивости — полный, с возвратом к среднему; новые сноски 12 и 13).
// Формализация — новые src/process/ProcessODELinearLaws.v и src/stdlib/trading/PriceDynamicsStability.v;
// прежние файлы не менялись.
// Запуск: node patch-p08-step-05-pages.cjs  (затем relocate + merge по part08-ch05). Скрипт повторяем.
// Внимание: L() превращает знак «¤» в обратную косую черту.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 23.11 (Часть VIII, шаг 5, слово автора)';
const KEPT = DONE + ' (формализацией; текст фразы не менялся): ';
const CL = 'Closed under the global context';
const LL = 'src/process/ProcessODELinearLaws.v';
const PS = 'src/stdlib/trading/PriceDynamicsStability.v';
const PD = 'src/stdlib/trading/PriceDynamicsODE.v';
const EL = 'src/process/ProcessExpLadder.v';
const GI = 'src/process/ProcessGronwallInequality.v';
const GS = 'src/process/ProcessPicardGridSolution.v';
const PO = 'src/process/ProcessPicardOperator.v';
const OE = 'src/process/ProcessODEExamples.v';
const SY = 'src/process/ProcessODESystem.v';
const FP = 'src/FixedPoint.v';
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
const INJ = 'inject_Z (Z.of_nat (S k))';
const N_EEM = 'exp_euler_is_euler_method : forall t0 y0 h n, euler_method (fun _ y => exp_rhs y) t0 y0 h n == exp_euler y0 h n (ProcessODELinearLaws.v:150); euler_method — общий метод Эйлера (ProcessODE.v:48), exp_euler y0 h n := y0 * Qpow (1 + h) n (ProcessODEExamples.v:76). Локальная рекурсия euler_yeqy — тот же процесс: euler_yeqy_is_exp_euler (:160); e-процесс — exp1_is_exp_euler (:168). ' + CL + '.';
const N_XEM = 'expt_is_euler_method : forall t N, expt_process t N == euler_method (fun _ y => exp_rhs y) 0 1 (t / inject_Z (Z.of_nat (S N))) (S N) (ProcessODELinearLaws.v:182) — стадия N есть траектория общего метода Эйлера уравнения y′ = y от 1 с шагом t/(N+1) за N+1 шаг. ' + CL + '.';
const N_CALL = 'expt_process_is_Cauchy_all : forall s, is_Cauchy (expt_process s) (ProcessODELinearLaws.v:418) — при всяком рациональном s; для s >= 0 — expt_process_is_Cauchy (ProcessExpLadder.v:565), для s <= 0 — expt_process_neg_is_Cauchy (:392). ' + CL + '.';
const N_NMOD = 'expt_neg_modulus : forall a k0, 0 <= a -> a < inject_Z (Z.of_nat (S k0)) -> forall N m n, (k0 <= N)%nat -> (N <= m)%nat -> (N <= n)%nat -> Qabs (expt_process (- a) m - expt_process (- a) n) <= 2 * (1 / qpow (1 - a / inject_Z (Z.of_nat (S k0))) (S k0)) * (a * a / inject_Z (Z.of_nat (S N))) (ProcessODELinearLaws.v:336); опора — (1 − a/n)^n (1 + a/n)^n = (1 − a²/n²)^n (expt_neg_times_pos, :251). ' + CL + '.';
const N_PMOD = 'expt_modulus (ProcessExpLadder.v:538): при 0 <= s < k0 + 1 и n >= k0 выполнено expt_process s m − expt_process s n <= B·s²/(n + 1), B = (1 − s/(k0+1))^(−(k0+1)). ' + CL + '.';
const N_E1 = 'exp1_increasing : forall N, exp1_process N < exp1_process (S N) (ProcessExpLadder.v:657); exp1_upper : forall N, exp1_process N < 3 (:601); вместе с нижней границей — exp1_ladder (:669). ' + CL + '.';
const N_E1C = 'exp1_is_Cauchy : is_Cauchy exp1_process (ProcessExpLadder.v:729); exp1_modulus : forall N0 m n, (N0 <= m)%nat -> (N0 <= n)%nat -> Qabs (exp1_process m - exp1_process n) < 3 / inject_Z (Z.of_nat (S N0)) (:699). ' + CL + '.';
const N_LC = 'linear_euler_closed : forall L t0 y0 h n, euler_method (fun _ y => L * y) t0 y0 h n == y0 * Qpow (1 + L * h) n (ProcessODELinearLaws.v:194) — при любом знаке L. ' + CL + '.';
const N_LG = 'linear_euler_gronwall : forall L t0 y0 h n, euler_method (fun _ y => L * y) t0 y0 h n == gronwall_iterate L 0 h y0 n (ProcessODELinearLaws.v:203). Прежняя лемма с похожим именем, linear_euler_is_gronwall (ProcessODEExamples.v:210), есть равенство терма самому себе. ' + CL + '.';
const N_LGR = 'linear_euler_growth : forall L t0 y0 h n, 0 < L -> 0 < h -> 0 < y0 -> euler_method (fun _ y => L * y) t0 y0 h n < euler_method (fun _ y => L * y) t0 y0 h (S n) (ProcessODELinearLaws.v:225). ' + CL + '.';
const N_LT = 'linear_euler_at_time : forall L t y0 k, euler_method (fun _ y => L * y) 0 y0 (t / ' + INJ + ') (S k) == y0 * expt_process (L * t) k (ProcessODELinearLaws.v:234) — n на странице есть k + 1. ' + CL + '.';
const N_LTC = 'linear_euler_at_time_is_Cauchy : forall L t y0, is_Cauchy (fun k => euler_method (fun _ y => L * y) 0 y0 (t / ' + INJ + ') (S k)) (ProcessODELinearLaws.v:430). ' + CL + '.';
const N_DC = 'decay_euler_closed : forall alpha t0 y0 h n, euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n == y0 * Qpow (1 - alpha * h) n (ProcessODELinearLaws.v:446); она же итерация Гронуолла с темпом −alpha — decay_euler_is_gronwall (:456). ' + CL + '.';
const N_DM = 'decay_euler_monotone : forall alpha t0 y0 h n, 0 <= 1 - alpha * h -> 1 - alpha * h <= 1 -> 0 <= y0 -> euler_method (fun _ y => decay_rhs alpha y) t0 y0 h (S n) <= euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n (ProcessODELinearLaws.v:466); сравнение с началом — decay_euler_bounded (:477). ' + CL + '.';
const N_DAM = 'decay_euler_abs_monotone : forall alpha t0 y0 h n, Qabs (1 - alpha * h) <= 1 -> Qabs (euler_method (fun _ y => decay_rhs alpha y) t0 y0 h (S n)) <= Qabs (euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n) (ProcessODELinearLaws.v:488) — начало любого знака; сравнение с началом — decay_euler_abs_bounded (:500). ' + CL + '.';
const N_DV = 'decay_euler_vanishes : forall alpha t0 y0 h, Qabs (1 - alpha * h) < 1 -> forall eps, 0 < eps -> exists N : nat, forall n, (N <= n)%nat -> Qabs (euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n) < eps (ProcessODELinearLaws.v:512). ' + CL + '.';
const N_DT = 'decay_euler_at_time : forall alpha t y0 k, euler_method (fun _ y => decay_rhs alpha y) 0 y0 (t / ' + INJ + ') (S k) == y0 * expt_process (- (alpha * t)) k (ProcessODELinearLaws.v:525); границы стадии — decay_euler_at_time_bounds (:550). ' + CL + '.';
const N_DTC = 'decay_euler_at_time_is_Cauchy : forall alpha t y0, is_Cauchy (fun k => euler_method (fun _ y => decay_rhs alpha y) 0 y0 (t / ' + INJ + ') (S k)) (ProcessODELinearLaws.v:538). ' + CL + '.';
const N_O2 = 'order2_second_difference : forall g h y0 v0 k, fst (order2_euler g h y0 v0 (S (S k))) - 2 * fst (order2_euler g h y0 v0 (S k)) + fst (order2_euler g h y0 v0 k) == h * h * g (tg h k) (fst (order2_euler g h y0 v0 k)) (snd (order2_euler g h y0 v0 k)) (ProcessODELinearLaws.v:604). ' + CL + '.';
const N_ES = 'sho_energy_step : forall h y0 v0 k, sho_E h y0 v0 (S k) == (1 + h * h) * sho_E h y0 v0 k (ProcessODELinearLaws.v:640); sho_E h y0 v0 n := y_n·y_n + v_n·v_n для sho_euler (:622). ' + CL + '.';
const N_EC = 'sho_energy_closed : forall h y0 v0 n, sho_E h y0 v0 n == Qpow (1 + h * h) n * sho_E h y0 v0 0 (ProcessODELinearLaws.v:647); число главы 10201/10000 = (1 + 1/100)² — sho_energy2_from_law (:707). ' + CL + '.';
const N_EST = 'sho_energy_strict : forall h y0 v0 k, ~ h == 0 -> 0 < sho_E h y0 v0 0 -> sho_E h y0 v0 k < sho_E h y0 v0 (S k) (ProcessODELinearLaws.v:689); нестрогий рост при любом шаге — sho_energy_nondecreasing (:667). ' + CL + '.';
const N_ED = 'sho_energy_at_time_drift : forall t y0 v0 k, 2 * (t * t) <= ' + INJ + ' -> sho_E (t / ' + INJ + ') y0 v0 (S k) - (y0 * y0 + v0 * v0) <= 2 * (t * t / ' + INJ + ') * (y0 * y0 + v0 * v0) (ProcessODELinearLaws.v:742) — n на странице есть k + 1. ' + CL + '.';
const N_EV = 'sho_energy_drift_vanishes : forall t y0 v0 eps, 0 < eps -> exists N : nat, forall k, (N <= k)%nat -> 0 <= sho_E (t / ' + INJ + ') y0 v0 (S k) - (y0 * y0 + v0 * v0) ' + AND + ' sho_E (t / ' + INJ + ') y0 v0 (S k) - (y0 * y0 + v0 * v0) < eps (ProcessODELinearLaws.v:772). Это утверждение о дрейфе энергии, а не о сохранении её какой-либо схемой. ' + CL + '.';
const N_V1 = 'sho_v1 : forall h, snd (sho_euler h 1 0 1) == - h (ProcessODELinearLaws.v:713) — из (y, v) = (1, 0) первый шаг даёт отрицательную скорость; вычисленная стадия sho_v2 (ProcessODESystem.v) — −1/5. Функций sin и cos в формализации нет: теорема говорит о знаке стадии. ' + CL + '.';
const N_PSUM = 'price_trajectory_sum : forall forces p, price_trajectory p forces == p + fold_right Qplus 0 forces (PriceDynamicsStability.v:86). ' + CL + '.';
const N_PSH = 'price_traj_shift : forall forces p q, price_trajectory p forces - price_trajectory q forces == p - q (PriceDynamicsStability.v:96) — коэффициент шага p |-> p + f по цене равен единице, сжатия нет. ' + CL + '.';
const N_PES = 'price_step_is_euler_step : forall p f t, price_step p f == euler_step (fun _ _ => f) t p 1 (PriceDynamicsStability.v:110) — шаг Эйлера с шагом сетки 1 и правой частью, не зависящей от цены. ' + CL + '.';
const N_PH = 'price_history_ex : map Qred (price_history p0_ex forces_ex) = [100; 101; 201 # 2; 405 # 4; 101; 203 # 2] (PriceDynamicsStability.v:103). ' + CL + '.';
const N_LCS = 'lipschitz_check_spec : forall L, lipschitz_check L = true <-> L <= 1 (PriceDynamicsStability.v:118) — нестрогое сравнение; lipschitz_check_at_one (:121): lipschitz_check 1 = true. ' + CL + '.';
const N_SSS = 'stability_signal_spec : forall L, stability_signal L <> (-1)%Z <-> L < 1 (PriceDynamicsStability.v:128); stability_signal_at_one (:124): stability_signal 1 = −1. ' + CL + '.';
const N_MD = 'mr_deviation : forall p0 target alpha n, mr_trajectory p0 target alpha n - target == (p0 - target) * Qpow (1 - alpha) n (PriceDynamicsStability.v:178); шаг — mr_step (:171); по модулю — mr_abs_deviation (:187). ' + CL + '.';
const N_MSL = 'mr_step_lipschitz : forall p q target alpha, Qabs ((p + mean_reverting_force p target alpha) - (q + mean_reverting_force q target alpha)) == Qabs (1 - alpha) * Qabs (p - q) (PriceDynamicsStability.v:195) — равенство: коэффициент шага есть в точности |1 − alpha|. ' + CL + '.';
const N_MLR = 'mr_lipschitz_ratio : forall p q target alpha, ~ p == q -> lipschitz_ratio p (p + mean_reverting_force p target alpha) q (q + mean_reverting_force q target alpha) == Qabs (1 - alpha) (PriceDynamicsStability.v:206). ' + CL + '.';
const N_MS = 'mr_stable : forall p0 target alpha n, Qabs (1 - alpha) <= 1 -> Qabs (mr_trajectory p0 target alpha n - target) <= Qabs (p0 - target) (PriceDynamicsStability.v:236); от шага к шагу — mr_stable_monotone (:244). ' + CL + '.';
const N_MSC = 'mr_stable_by_check : forall p0 target alpha, lipschitz_check (Qabs (1 - alpha)) = true -> forall n, Qabs (mr_trajectory p0 target alpha n - target) <= Qabs (p0 - target) (PriceDynamicsStability.v:257). ' + CL + '.';
const N_MC = 'mr_converges : forall p0 target alpha, Qabs (1 - alpha) < 1 -> forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> Qabs (mr_trajectory p0 target alpha n - target) < eps (PriceDynamicsStability.v:265). ' + CL + '.';
const N_MCS = 'mr_converges_by_signal : forall p0 target alpha, stability_signal (Qabs (1 - alpha)) <> (-1)%Z -> forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> Qabs (mr_trajectory p0 target alpha n - target) < eps (PriceDynamicsStability.v:294). ' + CL + '.';
const N_MM = 'mr_marginal_no_convergence : forall p0 target n, Qabs (mr_trajectory p0 target 2 n - target) == Qabs (p0 - target) (PriceDynamicsStability.v:319); проверка при этом проходит — mr_check_passes_at_two (:316). ' + CL + '.';
const N_MU = 'mr_unstable_grows : forall p0 target alpha n, 1 < Qabs (1 - alpha) -> ~ p0 == target -> Qabs (mr_trajectory p0 target alpha n - target) < Qabs (mr_trajectory p0 target alpha (S n) - target) (PriceDynamicsStability.v:328). ' + CL + '.';
const N_MCN = 'mr_map_is_contraction : forall target alpha R, Qabs (1 - alpha) < 1 -> 0 <= R -> is_contraction (mr_map target alpha) (target - R) (target + R) (Qabs (1 - alpha)) (PriceDynamicsStability.v:356); is_contraction — FixedPoint.v:47, тот же предикат, что у скалярной итерации Эйлера–Пикара; цель — неподвижная точка (mr_map_fixed, :168); траектория есть итерация шага (mr_trajectory_is_iterate, :161). ' + CL + '.';
const N_MG = 'mr_deviation_is_gronwall : forall p0 target alpha n, mr_trajectory p0 target alpha n - target == gronwall_iterate (- alpha) 0 1 (p0 - target) n (PriceDynamicsStability.v:377); сама траектория есть метод Эйлера с шагом 1 для p′ = alpha (target − p) — mr_trajectory_is_euler_method (:388). ' + CL + '.';
const N_SUPC = 'picard_iter_sup_cauchy (ProcessPicardGridSolution.v:611): при L·T < 1 итерации Пикара на сетке — процесс Коши в sup-норме. ' + CL + '.';
const NOOBJ = 'Чисел e^t, e^{−alpha t} и функций sin, cos как завершённых объектов в файлах главы нет (шапки ProcessODELinearLaws.v и ProcessExpLadder.v, раздел «NOT claimed»); сходимость векторного процесса осциллятора к траектории не записана.';
const ALL51 = 'все 51 объявление ProcessODELinearLaws.v: Closed under the global context';
const ALL33 = 'все 33 объявления PriceDynamicsStability.v: Closed under the global context';

// --- цитаты страницы после правок
const C11 = 'Глава 8.3 доказала, что оператор Пикара при $LT<1$ есть сжатие на пространстве грид-функций (сжимающий механизм и геометрическое сближение итератов), а Глава 8.4 разобрала устойчивость и Гронуолл.';
const C35A = 'Эти объекты — роль-пределы; завершённым объектом ни один из них здесь не предъявлен.';
const C35B = L('Сама $¤varepsilon$-сходимость аксиом не требует: лестница $(1+s/N)^N$ есть процесс Коши при всяком рациональном $s$, а дрейф энергии осциллятора к данному моменту $t$ становится меньше любого $¤varepsilon$ при измельчении сетки; для $¤sin$ и $¤cos$ утверждение о сходимости не записано.');
const C62 = 'При $L > 0$ — рост (множитель больше единицы), при $L < 0$ — затухание.[^12]';
const C66 = L('Здесь множитель шага есть $1 - ¤alpha h$, и при $0 ¤le 1 - ¤alpha h ¤le 1$ процесс с неотрицательным началом не растёт, а убывает — ровно случай затухающего Гронуолла из Главы 8.4: $u_{n+1} ¤le u_n ¤le u_0$; при начале любого знака убывает модуль.');
const C87 = L('При начале $(y, v) = (1, 0)$ его точное решение — $(¤cos t, -¤sin t)$, и эта траектория — роль-предел векторного Эйлерова процесса;');
const C98 = 'Закон дрейфа точен: каждый шаг умножает энергию на $1+h^2$; к данному моменту $t$ дрейф тем меньше, чем мельче сетка.';
const C121A = 'Файл вводит и проверку устойчивости через липшицев коэффициент — условие того же рода, что $LT<1$ сжатия Пикара (Глава 8.3), прочитанное как признак устойчивой динамики.';
const C121B = 'У самой динамики $p_{n+1} = p_n + f_n$ коэффициент равен единице: две траектории под одними воздействиями сохраняют расстояние.';
const C121C = L('Содержательна проверка для динамики возврата к среднему $p_{n+1} = p_n + ¤alpha(¤bar p - p_n)$: коэффициент шага равен $¤lvert 1-¤alpha¤rvert$; если он не больше единицы, отклонение от цели $¤bar p$ не растёт, если меньше — становится меньше любого $¤varepsilon$, если больше — растёт.[^13]');
const C143 = 'Над ними — гарантии: при липшицевости и $LT<1$ итерация сжимает (Глава 8.3), откуда Коши-сходимость процесса; при одной липшицевости расхождение контролируется по Гронуоллу (Глава 8.4).';
const C166 = L('*Доказано над ℚ без аксиом*: метод Эйлера и его конкретные траектории; оператор Пикара как сжатие на грид-функциях ($ℚ^{N+1}$, sup-метрика) при $LT<1$ с геометрическим зазором итератов; существование и единственность решения на сетке; пошаговый и геометрический контроль расхождения; неравенство Гронуолла и затухание; экспонента, линейные уравнения, осциллятор и динамика цены как конкретные рациональные процессы; $¤varepsilon$-сходимость итераций и множителей — свойство Коши самих процессов.');
const C171 = L('*Граница* (L3 / роль-предел): завершённые функции-решения, $e^t$, $¤sin$, $¤cos$ как объекты; глобальное во времени продолжение, blow-up, максимальный интервал.');
const F1 = 'Опорные файлы — `ProcessODEExamples.v` (экспонента `exp_rhs`, затухание `decay_rhs`, линейное), `ProcessExpProcess.v` ($e$-процесс), `ProcessExpLadder.v` (лестница $(1+s/N)^N$: рост, ограниченность, свойство Коши), `ProcessODESystem.v` (системы и осциллятор), `ProcessODELinearLaws.v` (траектории за $n$ шагов, затухание, закон энергии осциллятора), `PriceDynamicsODE.v` и `PriceDynamicsStability.v` (динамика цены и её устойчивость, каталог `stdlib/trading/`).';
const F1B = 'Все — 0 аксиом (`Print Assumptions`).';
const F2 = 'Что общий метод Эйлера с правой частью `exp_rhs` даёт именно `exp_euler` — `exp_euler_is_euler_method` (`ProcessODELinearLaws.v`), 0 аксиом.';
const F4 = 'Что стадии растут, лежат ниже тройки и образуют процесс Коши с явным модулем — `exp1_increasing`, `exp1_upper`, `exp1_is_Cauchy`, `exp1_modulus` в `ProcessExpLadder.v`, 0 аксиом.';
const F5A = "Стадия есть траектория Эйлера уравнения $y'=y$ с шагом $t/(N{+}1)$ — `expt_is_euler_method`; лестница есть процесс Коши при всяком рациональном $t$ — `expt_process_is_Cauchy_all` (оба — `ProcessODELinearLaws.v`);";
const F5B = L('при $t ¤ge 0$ явный модуль — `expt_modulus` (`ProcessExpLadder.v`), при $t ¤le 0$ — `expt_neg_modulus`. 0 аксиом.');
const F6A = L('Метод Эйлера с этой правой частью даёт $y_0(1-¤alpha h)^n$ — `decay_euler_closed`; убывание от шага к шагу при $0 ¤le 1-¤alpha h ¤le 1$ и $y_0 ¤ge 0$ — `decay_euler_monotone`; при начале любого знака и $¤lvert 1-¤alpha h¤rvert ¤le 1$ убывает модуль — `decay_euler_abs_monotone`; при $¤lvert 1-¤alpha h¤rvert < 1$ траектория стремится к нулю — `decay_euler_vanishes`.');
const F6B = L('В момент $t$ за $n$ шагов — стадия $y_0(1-¤alpha t/n)^n$ (`decay_euler_at_time`), и эти стадии образуют процесс Коши (`decay_euler_at_time_is_Cauchy`). Все — `ProcessODELinearLaws.v`, 0 аксиом.');
const F7 = "`sys_euler` в `ProcessODESystem.v`: векторный Эйлер для системы $y'=f_1$, $v'=f_2$; законы шага `sys_euler_fst_S`, `sys_euler_snd_S`. 0 аксиом.";
const F7B = 'Липшицевость, сжатие и оценка расхождения для систем в формализации не записаны.';
const F8 = 'Что позиция удовлетворяет разностному уравнению второго порядка $y_{k+2} - 2y_{k+1} + y_k = h^2 g(t_k, y_k, v_k)$ — `order2_second_difference` (`ProcessODELinearLaws.v`), 0 аксиом.';
const F9A = L('Общий закон: каждый шаг умножает энергию на $1+h^2$ при любых $h$ и начале (`sho_energy_step`), $E_n = (1+h^2)^n E_0$ (`sho_energy_closed`), рост строгий при $h ¤ne 0$ и ненулевом начале (`sho_energy_strict`).');
const F9B = L('К моменту $t$ за $n ¤ge 2t^2$ шагов дрейф не больше $2t^2/n$ от $E_0$ (`sho_energy_at_time_drift`) и становится меньше любого $¤varepsilon$ при измельчении сетки (`sho_energy_drift_vanishes`).');
const F9C = 'Знак скорости: из $(1, 0)$ первый шаг даёт $v_1 = -h$ (`sho_v1`). Все — `ProcessODELinearLaws.v`, 0 аксиом.';
const F9D = 'Сходимость самих пар $(y_n, v_n)$ к траектории не записана.';
const F10 = 'Совпадение с шагом Эйлера — `price_step_is_euler_step`; траектория есть начальная цена плюс сумма воздействий — `price_trajectory_sum` (оба — `PriceDynamicsStability.v`), 0 аксиом.';
const F11 = 'Все шесть стадий одним утверждением — `price_history_ex` (`PriceDynamicsStability.v`).';
const F12A = L('`linear_euler_step` в `ProcessODEExamples.v` — один шаг: $y ¤mapsto (1+Lh)y$. Траектория за $n$ шагов есть $y_0(1+Lh)^n$ (`linear_euler_closed`), она же однородная итерация Гронуолла (`linear_euler_gronwall`); при $L>0$, $h>0$, $y_0>0$ она строго растёт (`linear_euler_growth`).');
const F12B = 'В момент $t$ за $n$ шагов — стадия лестницы $y_0(1+Lt/n)^n$ (`linear_euler_at_time`), и эти стадии образуют процесс Коши при любых рациональных $L$, $t$, $y_0$ (`linear_euler_at_time_is_Cauchy`). Все — `ProcessODELinearLaws.v`, 0 аксиом.';
const F13A = L('`lipschitz_check` и `stability_signal` в `PriceDynamicsODE.v` — сравнения числа с порогами: `lipschitz_check L = true` равносильно $L ¤le 1$ (`lipschitz_check_spec`), а `stability_signal L` отличен от $-1$ в точности при $L<1$ (`stability_signal_spec`).');
const F13B = 'Для `price_trajectory` расстояние между траекториями сохраняется — `price_traj_shift`.';
const F13C = L('Для возврата к среднему (`mr_trajectory`): отклонение от цели на каждом шаге умножается на $1-¤alpha$ (`mr_deviation`), коэффициент шага — `mr_step_lipschitz`, он же `lipschitz_ratio` шага (`mr_lipschitz_ratio`);');
const F13D = L('из проверки следует, что отклонение не растёт (`mr_stable_by_check`), из сигнала — что траектория приходит к цели (`mr_converges_by_signal`); на пороге, при $¤alpha = 2$, проверка проходит, а отклонение сохраняет величину (`mr_marginal_no_convergence`); за порогом оно растёт (`mr_unstable_grows`).');
const F13E = L('Шаг возврата к среднему — сжатие в смысле `FixedPoint.v` (`mr_map_is_contraction`), а отклонение — однородная итерация Гронуолла с темпом $-¤alpha$ (`mr_deviation_is_gronwall`). Все — `PriceDynamicsStability.v` (`stdlib/trading/`), 0 аксиом.');

{
  const { fix, add, save, claimOf } = open('part08-ch05');

  // ------------------------------------------------------------ вводная часть
  fix('Глава 8.3 доказала, что оператор Пикара', 'picard_op_contraction', { claim: C11, assumptions: CL,
    note: DONE + ': названо условие сжатия. picard_op_contraction (ProcessPicardOperator.v:102): |Φy_k − Φz_k| <= (L·Tlen)·D на узлах k <= N; сжатием оценка становится при L * Tlen < 1 (посылка Hrate, :181). ' + CL + '.' });
  fix('Доказанное ядро — конкретные процессы над ℚ', null, { file: LL,
    note: KEPT + 'перечень теперь опирается на общие утверждения, а не только на объявления и вычисления: y′ = y — exp_euler_is_euler_method (ProcessODELinearLaws.v:150); затухание — decay_euler_closed (:446), decay_euler_monotone (:466); общее линейное — linear_euler_closed (:194); системы — order2_second_difference (:604); осциллятор — sho_energy_step (:640); цена — price_trajectory_sum (PriceDynamicsStability.v:86), mr_deviation (:178). Все — ' + CL + '.' });

  // ------------------------------------------------------------ «Чего глава не делает» (место 5.1)
  fix('Эти объекты — роль-пределы, и', 'iterate_is_cauchy', { theorem: 'expt_process_is_Cauchy_all', file: LL, claim: C35B, assumptions: CL, page_price: 'аксиом не требует',
    note: DONE + ': слова «наследует L3 (как в Главах 8.3–8.4)» сняты — цена названа по компилятору. ' + N_CALL + ' Те же утверждения Глав 8.3–8.4 (iterate_is_cauchy, FixedPoint.v:263; Qpow_vanish, SeriesConvergence.v:164) — ' + CL + '.' });
  add({ theorem: 'sho_energy_drift_vanishes', file: LL, assumptions: CL, claim: C35B, page_price: 'аксиом не требует',
    note: '«Дрейф энергии осциллятора к данному моменту t становится меньше любого ε при измельчении сетки»: ' + N_EV });
  add({ theorem: null, file: LL, claim: C35A,
    note: DONE + ': новая фраза. Статус честный. ' + NOOBJ });

  // ------------------------------------------------------------ «Экспонента как процесс»
  fix('Метод Эйлера для него особенно прозрачен', 'exp_euler', {
    note: 'exp_euler y0 h n := y0 * Qpow (1 + h) n (ProcessODEExamples.v:76) — замкнутая формула. Что рекурсия общего метода Эйлера с правой частью exp_rhs даёт именно её — exp_euler_is_euler_method (ProcessODELinearLaws.v:150); для локальной рекурсии — euler_yeqy_closed (ProcessExpProcess.v:71).' });
  add({ theorem: 'exp_euler_is_euler_method', file: LL, assumptions: CL, claim: claimOf('Метод Эйлера для него особенно прозрачен'),
    note: KEPT + '«за n шагов получается (1+h)^n» — о самом методе Эйлера: ' + N_EEM });
  fix('Достигая момента $t=1$ за $N$ шагов', 'exp1_lower', { assumptions: CL,
    note: 'Стадии — exp1_0, exp1_1, exp1_2 (ProcessExpProcess.v:58–65): 2, 9/4, 64/27; нижняя граница — exp1_lower (:129): forall N, 2 <= exp1_process N. С шага 1 Части VIII доказаны и рост, и граница сверху, и свойство Коши: ' + N_E1 + ' ' + N_E1C });
  fix('Для произвольного времени аналогично', 'expt_process', {
    note: 'expt_process t N := qpow (1 + t / inject_Z (Z.of_nat (S N))) (S N) (ProcessExpProcess.v:51) — стадия (1 + t/(N+1))^(N+1) при рациональном t. «Аналогично» теперь записано теоремами: стадия есть траектория Эйлера (expt_is_euler_method, ProcessODELinearLaws.v:182); лестница — процесс Коши при всяком рациональном t (expt_process_is_Cauchy_all, :418).' });
  add({ theorem: 'expt_process_is_Cauchy_all', file: LL, assumptions: CL, claim: claimOf('Для произвольного времени аналогично'),
    note: KEPT + '«e^t — роль-предел процесса (1+t/N)^N»: ' + N_CALL });
  add({ theorem: 'expt_is_euler_method', file: LL, assumptions: CL, claim: claimOf('Для произвольного времени аналогично'), note: N_XEM });

  // ------------------------------------------------------------ «Линейные уравнения» (место 5.2)
  fix(L("Уравнение $y' = L y$ — общее линейное однородное"), 'linear_euler_step', { assumptions: CL,
    note: 'linear_euler_step (ProcessODEExamples.v:216): euler_step (fun _ y => L * y) t y h == (1 + L * h) * y — один шаг, при любом L. Траектория за n шагов и «масштабированная экспонента» — в новом файле: linear_euler_closed (ProcessODELinearLaws.v:194), linear_euler_at_time (:234); сноска 12. ' + CL + '.' });
  add({ theorem: 'linear_euler_at_time', file: LL, assumptions: CL, claim: claimOf(L("Уравнение $y' = L y$ — общее линейное однородное")),
    note: KEPT + '«ведёт себя как масштабированная экспонента»: ' + N_LT });
  add({ theorem: 'linear_euler_growth', file: LL, assumptions: CL, claim: C62,
    note: DONE + ': к фразе поставлена сноска 12. «При L > 0 — рост»: ' + N_LGR + ' «При L < 0 — затухание»: траектория есть однородная итерация Гронуолла (linear_euler_gronwall, :203), и при |1 + L·h| <= 1 её модуль не растёт (gronwall_iterate_abs_decay, ProcessGronwallInequality.v:570); при L·h < −2 модуль растёт.' });
  fix(L('Здесь множитель шага есть $1 - ¤alpha h$'), 'gronwall_decay_factor', { theorem: 'decay_euler_monotone', file: LL, claim: C66, assumptions: CL,
    note: DONE + ': названо условие на начало, оценка записана шаг за шагом и для самого метода Эйлера. ' + N_DM + ' Без условия на начало формула неверна — decay_factor_needs_u0_nonneg (ProcessGronwallInequality.v:513).' });
  add({ theorem: 'decay_euler_abs_monotone', file: LL, assumptions: CL, claim: C66, note: '«При начале любого знака убывает модуль»: ' + N_DAM });
  add({ theorem: 'decay_euler_is_gronwall', file: LL, assumptions: CL, claim: C66,
    note: '«Ровно случай затухающего Гронуолла из Главы 8.4»: decay_euler_is_gronwall : forall alpha t0 y0 h n, euler_method (fun _ y => decay_rhs alpha y) t0 y0 h n == gronwall_iterate (- alpha) 0 h y0 n (ProcessODELinearLaws.v:456). ' + CL + '.' });

  // ------------------------------------------------------------ «Системы и осциллятор»
  add({ theorem: 'order2_second_difference', file: LL, assumptions: CL, claim: claimOf('Векторная форма позволяет свести *уравнение высшего порядка*'),
    note: KEPT + 'сведение записано и для второго порядка: ' + N_O2 + ' В формализации только второй порядок и только пары.' });
  add({ theorem: 'sho_v1', file: LL, assumptions: CL, claim: C87,
    note: DONE + ' (вопрос 1 шага 5, вариант 1): «(cos t, sin t)» → «при начале (1, 0) — (cos t, −sin t)». Для пары y′ = v, v′ = −y с y(0) = 1, v(0) = 0 вторая координата есть −sin t. ' + N_V1 });
  fix('Осциллятор обнажает и *честную* сторону численного метода', 'sho_energy_drifts', { assumptions: CL,
    note: 'sho_energy2 (ProcessODESystem.v:97) и sho_energy_drifts (:104) — вычисление на одном наборе чисел: E_2 == 10201 # 10000 и 1 < E_2. С шага 5 Части VIII это случай общего закона: ' + N_ES + ' ' + N_EC });
  add({ theorem: 'sho_energy_step', file: LL, assumptions: CL, claim: C98,
    note: DONE + ' (вопрос 2 шага 5, вариант 1): новая фраза в основном тексте. «Каждый шаг умножает энергию на 1 + h²»: ' + N_ES });
  add({ theorem: 'sho_energy_at_time_drift', file: LL, assumptions: CL, claim: C98,
    note: '«К данному моменту t дрейф тем меньше, чем мельче сетка»: ' + N_ED + ' Исчезновение — sho_energy_drift_vanishes (:772).' });

  // ------------------------------------------------------------ «Применения: динамика цены» (место 5.3)
  fix('Файл вводит и проверку устойчивости через липшицев коэффициент', 'lipschitz_check', { claim: C121A, assumptions: '',
    note: DONE + ' (вопрос 3 шага 5, вариант 1): слова «коэффициент сжатия меньше единицы» сняты — lipschitz_check L := Qle_bool L 1 (PriceDynamicsODE.v:38) есть «не больше единицы» (lipschitz_check_spec, PriceDynamicsStability.v:118). Связь проверки с траекторией теперь записана теоремами — следующие фразы абзаца и сноска 13.' });
  add({ theorem: 'lipschitz_check_spec', file: PS, assumptions: CL, claim: C121A, note: N_LCS });
  add({ theorem: 'price_traj_shift', file: PS, assumptions: CL, claim: C121B, note: DONE + ': новая фраза. ' + N_PSH });
  add({ theorem: 'mr_step_lipschitz', file: PS, assumptions: CL, claim: C121C, note: DONE + L(': новая фраза. «Коэффициент шага равен $¤lvert 1-¤alpha¤rvert$»: ') + N_MSL });
  add({ theorem: 'mr_stable', file: PS, assumptions: CL, claim: C121C, note: '«Если он не больше единицы, отклонение от цели не растёт»: ' + N_MS });
  add({ theorem: 'mr_converges', file: PS, assumptions: CL, claim: C121C, note: '«Если меньше — становится меньше любого ε»: ' + N_MC });
  add({ theorem: 'mr_unstable_grows', file: PS, assumptions: CL, claim: C121C, note: '«Если больше — растёт»: ' + N_MU });

  // ------------------------------------------------------------ синтез Части (место 5.1)
  fix('Над ними — гарантия: при липшицевости итерация сжимает', 'euler_picard_cauchy', { theorem: 'picard_op_contraction', file: PO, claim: C143, assumptions: CL,
    note: DONE + ': у каждой гарантии названо её условие. Сжатие — picard_op_contraction (ProcessPicardOperator.v:102), коэффициент L·T меньше единицы при L·T < 1. Коши-сходимость — picard_iter_sup_cauchy (ProcessPicardGridSolution.v:611) и euler_picard_cauchy_lip (ProcessPicardLipschitz.v:142). Контроль расхождения по Гронуоллу условия L·T < 1 не берёт — euler_divergence_gronwall (ProcessGronwallInequality.v:227). ' + CL + '.' });
  add({ theorem: 'picard_iter_sup_cauchy', file: GS, assumptions: CL, claim: C143, note: '«Откуда Коши-сходимость процесса»: ' + N_SUPC });
  add({ theorem: 'euler_divergence_gronwall', file: GI, assumptions: CL, claim: C143,
    note: '«При одной липшицевости расхождение контролируется по Гронуоллу»: euler_divergence_gronwall (ProcessGronwallInequality.v:227): Qabs (euler f h y0 n - euler f h z0 n) <= gronwall_iterate L 0 h (Qabs (y0 - z0)) n; посылки — 0 <= L, липшицевость f по y, 0 <= h. ' + CL + '.' });
  fix('*Доказано над ℚ без аксиом*: метод Эйлера и его конкретные траектории', null, { claim: C166, file: PO, page_price: 'без аксиом',
    note: DONE + ': перечень приведён к теоремам Части. Сжатие при L·T < 1 и зазор — picard_op_contraction, picard_iter_gap (ProcessPicardOperator.v:102, :234); существование и единственность на сетке без условия на L·T — picard_fixed_exists, picard_unique_any_rate (ProcessPicardGridSolution.v:243, :330); контроль расхождения — euler_step_diff, euler_diff_bound (ProcessODEStability.v:64, :86); неравенство Гронуолла и затухание — gronwall_inequality, gronwall_iterate_decay (ProcessGronwallInequality.v:104, :523); ε-сходимость итераций и множителей — picard_iter_sup_cauchy (ProcessPicardGridSolution.v:611), expt_process_is_Cauchy_all, decay_euler_vanishes (ProcessODELinearLaws.v:418, :512). Все — ' + CL + '.' });
  add({ theorem: 'picard_iter_sup_cauchy', file: GS, assumptions: CL, claim: C166, page_price: 'без аксиом', note: L('«$¤varepsilon$-сходимость итераций — свойство Коши самих процессов»: ') + N_SUPC });
  add({ theorem: 'expt_process_is_Cauchy_all', file: LL, assumptions: CL, claim: C166, page_price: 'без аксиом', note: L('«$¤varepsilon$-сходимость множителей — свойство Коши самих процессов»: ') + N_CALL });
  add({ theorem: 'picard_unique_any_rate', file: GS, assumptions: CL, claim: C166, page_price: 'без аксиом',
    note: '«Существование и единственность решения на сетке»: picard_fixed_exists (ProcessPicardGridSolution.v:243) и picard_unique_any_rate (:330) — без условия на L·T; при L·T < 1 через конечный максимум — picard_unique (ProcessPicardOperator.v:183). ' + CL + '.' });
  add({ theorem: 'gronwall_inequality', file: GI, assumptions: CL, claim: C166, page_price: 'без аксиом',
    note: '«Неравенство Гронуолла»: gronwall_inequality (ProcessGronwallInequality.v:104) — для произвольной последовательности под рекуррентной оценкой при неотрицательном множителе. ' + CL + '.' });
  fix(L('*Граница* (L3 / роль-предел): $¤varepsilon$-сходимость итераций'), 'decay_converges', { theorem: null, file: LL, claim: C171, assumptions: '', page_price: 'L3 / роль-предел',
    note: DONE + ': из перечня границы снята ε-сходимость итераций и множителей — она доказана без аксиом (decay_converges, ProcessODEExamples.v:139; expt_process_is_Cauchy_all, ProcessODELinearLaws.v:418; picard_iter_sup_cauchy, ProcessPicardGridSolution.v:611). Оставшееся — статус честный: ' + NOOBJ + ' Слово «L3» в заголовке перечня — тезис автора (Глава 8.1, § «Где появляется граница»).' });

  // ------------------------------------------------------------ сноска 1
  fix('Опорные файлы — `ProcessODEExamples.v`', 'exp_rhs', { claim: F1,
    note: DONE + ': названы три новых опорных файла, слова «батч C», «батч A» сняты. Семь файлов есть: src/process/ProcessODEExamples.v (20 Qed), ProcessExpProcess.v (12), ProcessExpLadder.v (44), ProcessODESystem.v (8), ProcessODELinearLaws.v (50), src/stdlib/trading/PriceDynamicsODE.v (23), PriceDynamicsStability.v (32). exp_rhs — Definition (ProcessODEExamples.v:49).' });
  fix('Новые файлы — 0 аксиом', null, { claim: F1B, page_price: '0 аксиом', assumptions: ALL51 + '; ' + ALL33,
    note: DONE + ': «Новые файлы» → «Все». Print Assumptions всех объявлений семи файлов сноски — Closed under the global context (четыре прежних — пробный файл PA.v первой вычитки; ProcessExpLadder.v — шаг 1; два новых — _p08step5/VerifyA.out, VerifyB.out). Строк Axiom, Parameter, Admitted в них нет.' });
  add({ theorem: null, file: EL, claim: F1, note: 'Файл src/process/ProcessExpLadder.v (шаг 1 Части VIII): 44 Qed; рост — expt_monotone (:396), ограниченность — expt_bounded (:519), свойство Коши — expt_process_is_Cauchy (:565), exp1_is_Cauchy (:729).' });
  add({ theorem: null, file: LL, claim: F1, assumptions: ALL51, note: DONE + ': новый опорный файл. src/process/ProcessODELinearLaws.v: 50 Qed и одно определение (sho_E); строк Axiom, Parameter, Admitted нет.' });
  add({ theorem: null, file: PS, claim: F1, assumptions: ALL33, note: DONE + ': новый опорный файл. src/stdlib/trading/PriceDynamicsStability.v: 32 Qed и одно определение (mr_map); строк Axiom, Parameter, Admitted нет.' });

  // ------------------------------------------------------------ сноски 2, 4, 5, 6
  add({ theorem: 'exp_euler_is_euler_method', file: LL, assumptions: CL, claim: F2, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_EEM });
  add({ theorem: 'exp1_increasing', file: EL, assumptions: CL, claim: F4, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_E1 });
  add({ theorem: 'exp1_upper', file: EL, assumptions: CL, claim: F4, page_price: '0 аксиом', note: N_E1 });
  add({ theorem: 'exp1_is_Cauchy', file: EL, assumptions: CL, claim: F4, page_price: '0 аксиом', note: N_E1C });
  add({ theorem: 'exp1_modulus', file: EL, assumptions: CL, claim: F4, page_price: '0 аксиом', note: N_E1C });
  add({ theorem: 'expt_is_euler_method', file: LL, assumptions: CL, claim: F5A, note: DONE + ': новая фраза. ' + N_XEM });
  add({ theorem: 'expt_process_is_Cauchy_all', file: LL, assumptions: CL, claim: F5A, note: N_CALL });
  add({ theorem: 'expt_modulus', file: EL, assumptions: CL, claim: F5B, page_price: '0 аксиом', note: N_PMOD });
  add({ theorem: 'expt_neg_modulus', file: LL, assumptions: CL, claim: F5B, page_price: '0 аксиом', note: N_NMOD });
  add({ theorem: 'decay_euler_closed', file: LL, assumptions: CL, claim: F6A, note: DONE + ': новая фраза. ' + N_DC });
  add({ theorem: 'decay_euler_monotone', file: LL, assumptions: CL, claim: F6A, note: N_DM });
  add({ theorem: 'decay_euler_abs_monotone', file: LL, assumptions: CL, claim: F6A, note: N_DAM });
  add({ theorem: 'decay_euler_vanishes', file: LL, assumptions: CL, claim: F6A, note: N_DV });
  add({ theorem: 'decay_euler_at_time', file: LL, assumptions: CL, claim: F6B, page_price: '0 аксиом', note: N_DT });
  add({ theorem: 'decay_euler_at_time_is_Cauchy', file: LL, assumptions: CL, claim: F6B, page_price: '0 аксиом', note: N_DTC });

  // ------------------------------------------------------------ сноски 7, 8, 9
  fix('`sys_euler` в `ProcessODESystem.v` (батч A)', 'sys_euler_fst_S', { claim: F7, assumptions: CL, page_price: '0 аксиом' });
  fix('`sys_euler` в `ProcessODESystem.v` (батч A)', 'sys_euler_snd_S', { claim: F7, assumptions: CL, page_price: '0 аксиом' });
  add({ theorem: null, file: SY, claim: F7B,
    note: DONE + ': новая фраза. Статус честный: в ProcessODESystem.v и ProcessODELinearLaws.v о парах записаны законы шага, первое уравнение редукции порядка, разностное уравнение второго порядка и закон энергии осциллятора; липшицевости, сжатия и оценки расхождения для систем нет.' });
  add({ theorem: 'order2_second_difference', file: LL, assumptions: CL, claim: F8, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_O2 });
  add({ theorem: 'sho_energy_step', file: LL, assumptions: CL, claim: F9A, note: DONE + ': новая фраза. ' + N_ES });
  add({ theorem: 'sho_energy_closed', file: LL, assumptions: CL, claim: F9A, note: N_EC });
  add({ theorem: 'sho_energy_strict', file: LL, assumptions: CL, claim: F9A, note: N_EST });
  add({ theorem: 'sho_energy_at_time_drift', file: LL, assumptions: CL, claim: F9B, note: N_ED });
  add({ theorem: 'sho_energy_drift_vanishes', file: LL, assumptions: CL, claim: F9B, note: N_EV });
  add({ theorem: 'sho_v1', file: LL, assumptions: CL, claim: F9C, page_price: '0 аксиом', note: N_V1 });
  add({ theorem: null, file: LL, claim: F9D, note: DONE + ': новая фраза, горизонт назван. Статус честный: ' + NOOBJ });

  // ------------------------------------------------------------ сноски 10, 11
  add({ theorem: 'price_step_is_euler_step', file: PS, assumptions: CL, claim: F10, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_PES });
  add({ theorem: 'price_trajectory_sum', file: PS, assumptions: CL, claim: F10, page_price: '0 аксиом', note: N_PSUM });
  add({ theorem: 'price_history_ex', file: PS, assumptions: CL, claim: F11, note: DONE + ': новая фраза. ' + N_PH });

  // ------------------------------------------------------------ сноска 12 (новая)
  add({ theorem: 'linear_euler_step', file: OE, assumptions: CL, claim: F12A,
    note: DONE + ': новая сноска. linear_euler_step (ProcessODEExamples.v:216): euler_step (fun _ y => L * y) t y h == (1 + L * h) * y. ' + CL + '.' });
  add({ theorem: 'linear_euler_closed', file: LL, assumptions: CL, claim: F12A, note: N_LC });
  add({ theorem: 'linear_euler_gronwall', file: LL, assumptions: CL, claim: F12A, note: N_LG });
  add({ theorem: 'linear_euler_growth', file: LL, assumptions: CL, claim: F12A, note: N_LGR });
  add({ theorem: 'linear_euler_at_time', file: LL, assumptions: CL, claim: F12B, page_price: '0 аксиом', note: N_LT });
  add({ theorem: 'linear_euler_at_time_is_Cauchy', file: LL, assumptions: CL, claim: F12B, page_price: '0 аксиом', note: N_LTC });

  // ------------------------------------------------------------ сноска 13 (новая)
  add({ theorem: 'lipschitz_check', file: PD, claim: F13A,
    note: DONE + ': новая сноска. Definition lipschitz_check (L : Q) : bool := Qle_bool L 1 (PriceDynamicsODE.v:38).' });
  add({ theorem: 'stability_signal', file: PD, claim: F13A,
    note: 'Definition stability_signal (L : Q) : Z (PriceDynamicsODE.v:43): 1 при L < 1/2, 0 при 1/2 <= L < 1, −1 при 1 <= L.' });
  add({ theorem: 'lipschitz_check_spec', file: PS, assumptions: CL, claim: F13A, note: N_LCS });
  add({ theorem: 'stability_signal_spec', file: PS, assumptions: CL, claim: F13A, note: N_SSS });
  add({ theorem: 'price_trajectory', file: PD, claim: F13B, note: 'Fixpoint price_trajectory (PriceDynamicsODE.v:19): рекурсия по списку воздействий.' });
  add({ theorem: 'price_traj_shift', file: PS, assumptions: CL, claim: F13B, note: N_PSH });
  add({ theorem: 'mr_trajectory', file: PD, claim: F13C,
    note: 'Fixpoint mr_trajectory p0 target alpha n (PriceDynamicsODE.v:170): следующая цена есть prev + mean_reverting_force prev target alpha, где mean_reverting_force p target alpha := alpha * (target - p) (:153).' });
  add({ theorem: 'mr_deviation', file: PS, assumptions: CL, claim: F13C, note: N_MD });
  add({ theorem: 'mr_step_lipschitz', file: PS, assumptions: CL, claim: F13C, note: N_MSL });
  add({ theorem: 'lipschitz_ratio', file: PD, claim: F13C,
    note: 'Definition lipschitz_ratio (x1 y1 x2 y2 : Q) : Q := Qabs (y2 - y1) / Qabs (x2 - x1) (PriceDynamicsODE.v:35); при совпадающих абсциссах равно нулю — lipschitz_ratio_degenerate (PriceDynamicsStability.v:142).' });
  add({ theorem: 'mr_lipschitz_ratio', file: PS, assumptions: CL, claim: F13C, note: N_MLR });
  add({ theorem: 'mr_stable_by_check', file: PS, assumptions: CL, claim: F13D, note: N_MSC });
  add({ theorem: 'mr_converges_by_signal', file: PS, assumptions: CL, claim: F13D, note: N_MCS });
  add({ theorem: 'mr_marginal_no_convergence', file: PS, assumptions: CL, claim: F13D, note: N_MM });
  add({ theorem: 'mr_unstable_grows', file: PS, assumptions: CL, claim: F13D, note: N_MU });
  add({ theorem: 'mr_map_is_contraction', file: PS, assumptions: CL, claim: F13E, page_price: '0 аксиом', note: N_MCN });
  add({ theorem: 'mr_deviation_is_gronwall', file: PS, assumptions: CL, claim: F13E, page_price: '0 аксиом', note: N_MG });
  add({ theorem: null, file: FP, claim: F13E, note: 'Файл src/FixedPoint.v: Definition is_contraction (:47) — предикат сжатия на отрезке рациональных чисел; на него опирается mr_map_is_contraction.' });

  save();
}
