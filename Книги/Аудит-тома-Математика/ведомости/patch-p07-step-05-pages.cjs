// Часть VII, шаг 5, страницы (2026-11-18, слово автора «Продолжай»): 7 правок главы VII.4 внесены
// (сходимость ряда Фурье по стандартной системе при нефиксированном усечении; Рисс — Фишер при фиксированном N;
//  сноски 1, 2 и новая 9).
// Формализация — новый src/process/ProcessFourierConvergenceStd.v; прежние файлы не менялись.
// Запуск: node patch-p07-step-05-pages.cjs  (затем relocate + merge по part07-ch04). Скрипт повторяем.
// Внимание: строки с настоящим знаком параграфа через L() не пропускать (здесь знак параграфа — PAR).
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 18.11 (Часть VII, шаг 5, слово автора)';
const CL = 'Closed under the global context';
const FC = 'src/process/ProcessFourierConvergenceStd.v';
const RF = 'src/process/ProcessL2RieszFischer.v';
const LO = 'src/process/ProcessL2Orthonormal.v';
const BS = String.fromCharCode(92);
const PAR = String.fromCharCode(167);
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

// --- утверждения (номера строк — src/process/ProcessFourierConvergenceStd.v, если не сказано иное)
const N_IFF = 'std_fourier_l2_convergence_iff : forall f : nat -> Q, is_Cauchy (fun n => captured f n) <-> (forall eps, 0 < eps -> exists M, forall K N, (M <= K)%nat -> ferr delta f N K < eps) (:182); прямая сторона — std_fourier_tail_to_zero (:152), обратная — std_fourier_tail_to_zero_conv (:166). Здесь captured f n = Σ_{i<n} f_i², ferr delta f N K — квадрат ошибки K-членной частичной суммы стандартной системы на N координатах; стадия M не зависит от N. ' + CL + '.';
const N_TAIL = 'std_error_is_tail : forall f N K, (K <= N)%nat -> ferr delta f N K == captured f N - captured f K (:133); std_error_zero_beyond : forall f N K, (N <= K)%nat -> ferr delta f N K == 0 (:140). ' + CL + '.';
const N_CAU = "std_partial_sums_cauchy : forall f, is_Cauchy (fun n => captured f n) -> forall eps, 0 < eps -> exists M, forall N K K', (M <= K)%nat -> (M <= K')%nat -> seq_inner (fun i => std_psum f N K i - std_psum f N K' i) (fun i => std_psum f N K i - std_psum f N K' i) N <= eps (:201); std_psum f N K — K-членная частичная сумма стандартной системы как вектор (:196); стадия M стоит до квантора по N. " + CL + '.';
const N_L2C = 'std_partial_sums_L2CauchySq : forall f N, is_Cauchy (fun n => captured f n) -> L2CauchySq (std_psum f N) N (:225) — посылка l2_riesz_fischer (ProcessL2RieszFischer.v:134) для частичных сумм, при каждом N. ' + CL + '.';
const N_LIM = 'std_limit_is_f : forall f N m s, (m < N)%nat -> (m < s)%nat -> l2_limit (std_psum f N) m s == f m (:233): координата m построенного предела с некоторой стадии равна f m. ' + CL + '.';
const N_SRF = 'std_fourier_riesz_fischer (:245): при процессе энергии Коши — (forall i, i < N -> is_Cauchy (l2_limit (std_psum f N) i)) ' + AND + ' (forall n, is_Cauchy (dist_to_limit (std_psum f N) N n)) ' + AND + ' (forall eps > 0, exists M, forall n >= M, exists S, forall s >= S, dist_to_limit (std_psum f N) N n s <= eps); получена из riesz_fischer_process_form (ProcessL2Orthonormal.v:618). ' + CL + '.';
const N_FIN = 'finite_support_energy_cauchy : forall f n0, (forall i, (n0 <= i)%nat -> f i == 0) -> is_Cauchy (fun n => captured f n) (:270). ' + CL + '.';
const N_GEO = 'geometric_energy_cauchy : is_Cauchy (fun n => captured half_pow n) (:330), где half_pow i = 2^(−i) (:281); замкнутая форма — geometric_energy_closed : 3 * captured half_pow n == 4 - 4 * (half_pow n * half_pow n) (:304); geometric_fourier_converges : forall eps, 0 < eps -> exists M, forall K N, (M <= K)%nat -> ferr delta half_pow N K < eps (:360). ' + CL + '.';
const N_RFH = 'rf_conclusion_is_hypothesis : forall F N, L2CauchySq F N <-> (forall eps, eps > 0 -> exists M, forall n s, (M <= n)%nat -> (M <= s)%nat -> seq_inner (fun i => F n i - l2_limit F i s) (fun i => F n i - l2_limit F i s) N <= eps) (:372); доказательство — split; intro H; exact H: обе стороны совпадают по определению l2_limit. ' + CL + '.';
const N_RF = 'Theorem l2_riesz_fischer (ProcessL2RieszFischer.v:134): L2CauchySq F N -> forall eps > 0, exists M, forall n s >= M, ‖F n − l2_limit F · s‖²_N <= eps — при фиксированном N (L2CauchySq F N, :87); l2_limit F i s = F s i (:112). ' + CL + '.';
const N_RFP = 'riesz_fischer_process_form (ProcessL2Orthonormal.v:618): при L2CauchySq F N — координаты предела суть процессы Коши, расстояние до предела dist_to_limit (:547) есть процесс Коши и стремится к нулю. ' + CL + '.';

{
  const { fix, add, save } = open('part07-ch04');
  // --- правка 1: второй уровень
  const C43 = L('*Второй* — процессное чтение: ряд Фурье как процесс $K§mapsto P_K$ с убывающей ошибкой; для стандартной системы доказано и большее — остаток стремится к нулю при всех усечениях $N$ сразу тогда и только тогда, когда процесс энергии $§sum_{i<n}f_i^2$ есть процесс Коши, и тогда частичные суммы L<sup>2</sup>-Коши, а предел, построенный по Риссу–Фишеру Части VI, есть сама $f$.');
  fix(L('*Второй* — процессное чтение: ряд Фурье как процесс $K§mapsto P_K$ с убывающей ошибкой, L<sup>2</sup>-полнота'), 'l2_riesz_fischer', { theorem: 'std_fourier_l2_convergence_iff', file: FC, claim: C43, assumptions: CL,
    note: DONE + ': было «L²-полнота по построению (Рисс–Фишер Части VI)» — теорема Рисса — Фишера верна при фиксированном усечении и к частичным суммам не применялась. Теперь для стандартной системы названо доказанное. ' + N_IFF });
  add({ theorem: 'std_partial_sums_cauchy', file: FC, claim: C43, note: N_CAU });
  add({ theorem: 'std_limit_is_f', file: FC, claim: C43, note: N_LIM });
  // --- правка 2: бюджет энергии
  const C111 = L('Для стандартной системы оно доказано в процессной форме: остаток $§norm{f-P_K}^2$ меньше любого $§varepsilon$ при всех усечениях $N$ сразу, начиная с некоторого $K$, тогда и только тогда, когда процесс энергии $n§mapsto§sum_{i<n}f_i^2$ есть процесс Коши.[^9]');
  add({ theorem: 'std_fourier_l2_convergence_iff', file: FC, claim: C111, note: N_IFF });
  // --- правка 3: Рисс — Фишер при фиксированном усечении; недостающие звенья
  fix('Здесь и помогает Рисс–Фишер из Части VI: *если* такой Коши-процесс частичных сумм', 'l2_riesz_fischer', { assumptions: CL,
    claim: 'Здесь и помогает Рисс–Фишер из Части VI: *если* такой Коши-процесс частичных сумм построен, его предел читается как L<sup>2</sup>-процесс (пространство L<sup>2</sup>-процессов Коши-полно по построению — при каждом фиксированном усечении $N$).[^2]',
    note: DONE + ': на странице оговорено фиксированное усечение. ' + N_RF + ' Содержательная форма — ' + N_RFP });
  const C116 = 'Но сама Коши-сходимость ряда Фурье к $f$ из одного Бесселя *не* следует: она требует полноты системы и сходимости процесса энергии.';
  add({ theorem: 'std_fourier_tail_to_zero_conv', file: FC, claim: C116,
    note: 'std_fourier_tail_to_zero_conv : forall f, (forall eps, 0 < eps -> exists M, forall K N, (M <= K)%nat -> ferr delta f N K < eps) -> is_Cauchy (fun n => captured f n) (:166): для стандартной системы сходимость остатка при всех усечениях влечёт, что процесс энергии есть процесс Коши, — условие необходимо. ' + CL + '.' });
  const C118 = 'Для стандартной системы оба недостающих звена доказаны: при процессе энергии Коши частичные суммы образуют L<sup>2</sup>-Коши-процесс со стадией, не зависящей от $N$, и координаты построенного предела совпадают с координатами $f$.';
  add({ theorem: 'std_partial_sums_cauchy', file: FC, claim: C118, note: N_CAU });
  add({ theorem: 'std_limit_is_f', file: FC, claim: C118, note: N_LIM });
  // --- правка 4: граница
  const C190 = 'Для стандартной системы оно доказано в процессной форме (' + PAR + ' «Энергетический бюджет, не гарантия предела»); для произвольной — остаётся границей.';
  add({ theorem: 'std_fourier_l2_convergence_iff', file: FC, claim: C190,
    note: N_IFF + ' Для произвольной ортонормированной системы при нефиксированном усечении такой теоремы в src нет: полные системы для неограниченного N, кроме стандартной, не построены.' });
  // --- сноска 1
  const F1 = 'Процессное чтение предела — `ProcessL2RieszFischer.v` и `ProcessFourierConvergenceStd.v` (26 утверждений, 0 аксиом).';
  fix('Процессное чтение предела — `ProcessL2RieszFischer.v`', null, { claim: F1,
    note: DONE + ': добавлен новый файл. ProcessFourierConvergenceStd.v подключает ProcessL2RieszFischer.v и ProcessL2Orthonormal.v и применяет Рисса — Фишера к частичным суммам стандартной системы (std_fourier_riesz_fischer, :245). Прежние опорные файлы ProcessFourierSeriesL2.v и ProcessBestApproximation.v файл ProcessL2RieszFischer.v не подключают.' }, RF);
  add({ theorem: null, file: FC, page_price: '0 аксиом', assumptions: 'все 28 объявлений файла: ' + CL, claim: F1,
    note: 'В ProcessFourierConvergenceStd.v 26 строк Qed и два определения (std_psum, half_pow); Admitted, Axiom, Parameter нет; все объявления — ' + CL + '.' });
  // --- сноска 2
  const F2a = 'Процессное прочтение Рисса–Фишера — `l2_riesz_fischer` в `ProcessL2RieszFischer.v` (Часть VI), при фиксированном усечении $N$: предел строится покоординатно как процесс (`l2_limit`), и заключение теоремы есть её посылка, развёрнутая по этому определению (`rf_conclusion_is_hypothesis`), — «полно по построению» в точном смысле;';
  fix('Процессное прочтение Рисса–Фишера — `l2_riesz_fischer` в `ProcessL2RieszFischer.v` (Часть VI)', 'l2_riesz_fischer', { claim: F2a, assumptions: CL,
    note: DONE + ': было «L²-пространство процессов Коши-полно по построению; это мост к носителю предела» — без оговорки об усечении и о том, что заключение совпадает с посылкой. ' + N_RF });
  add({ theorem: 'l2_limit', file: RF, claim: F2a, note: 'Definition l2_limit (F : nat -> nat -> Q) : nat -> (nat -> Q) := fun i s => F s i (ProcessL2RieszFischer.v:112): координата i предела есть процесс s ↦ F s i. ' + CL + '.' });
  add({ theorem: 'rf_conclusion_is_hypothesis', file: FC, claim: F2a, note: N_RFH });
  add({ theorem: 'riesz_fischer_process_form', file: LO, claim: 'содержательная трёхчастная форма — `riesz_fischer_process_form` (`ProcessL2Orthonormal.v`).', note: N_RFP });
  const F2c = 'Для частичных сумм стандартной системы посылка моста доказана — `std_partial_sums_L2CauchySq`, а предел опознан — `std_limit_is_f` (`ProcessFourierConvergenceStd.v`).';
  add({ theorem: 'std_partial_sums_L2CauchySq', file: FC, claim: F2c, note: N_L2C });
  add({ theorem: 'std_limit_is_f', file: FC, claim: F2c, note: N_LIM });
  // --- сноска 9
  const F9a = L('Для стандартной системы ошибка на $N$ координатах есть кусок энергии: $§norm{f-P_K}^2=§sum_{K§le i<N}f_i^2$ при $K§le N$ (`std_error_is_tail`) и нуль при $N§le K$ (`std_error_zero_beyond`).');
  add({ theorem: 'std_error_is_tail', file: FC, claim: F9a, note: N_TAIL });
  add({ theorem: 'std_error_zero_beyond', file: FC, claim: F9a, note: N_TAIL });
  const F9b = L('Отсюда `std_fourier_l2_convergence_iff`: процесс энергии есть процесс Коши $§Leftrightarrow$ для всякого $§varepsilon>0$ есть $M$, после которого ошибка меньше $§varepsilon$ при всех $K§ge M$ и всех $N$.');
  add({ theorem: 'std_fourier_l2_convergence_iff', file: FC, claim: F9b, note: N_IFF });
  const F9c = 'Тогда частичные суммы L<sup>2</sup>-Коши со стадией, не зависящей от $N$ (`std_partial_sums_cauchy`), посылка Рисса–Фишера выполнена (`std_partial_sums_L2CauchySq`, `std_fourier_riesz_fischer`), а координаты предела суть координаты $f$ (`std_limit_is_f`).';
  add({ theorem: 'std_partial_sums_cauchy', file: FC, claim: F9c, note: N_CAU });
  add({ theorem: 'std_partial_sums_L2CauchySq', file: FC, claim: F9c, note: N_L2C });
  add({ theorem: 'std_fourier_riesz_fischer', file: FC, claim: F9c, note: N_SRF });
  add({ theorem: 'std_limit_is_f', file: FC, claim: F9c, note: N_LIM });
  const F9d = 'Условие выполнимо: конечный носитель (`finite_support_energy_cauchy`) и $f_i=2^{-i}$ (`geometric_energy_cauchy`, `geometric_fourier_converges`).';
  add({ theorem: 'finite_support_energy_cauchy', file: FC, claim: F9d, note: N_FIN });
  add({ theorem: 'geometric_energy_cauchy', file: FC, claim: F9d, note: N_GEO });
  add({ theorem: 'geometric_fourier_converges', file: FC, claim: F9d, note: N_GEO });
  add({ theorem: null, file: null, claim: 'Что процесс энергии всякой $f$ с ограниченной энергией есть процесс Коши, не утверждается.',
    note: 'статус: такой теоремы в ProcessFourierConvergenceStd.v нет; посылка «процесс энергии есть процесс Коши» стоит в теоремах явно. Переход от ограниченной монотонной последовательности к процессу Коши без классической логики не выводится (шапка файла, раздел «NOT claimed»).' });
  save();
}
