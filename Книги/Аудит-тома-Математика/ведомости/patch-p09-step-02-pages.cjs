// Часть IX, шаг 2, страницы (2026-11-23, слово автора «Коммит и затем продолжай»): 12 правок глав IX.4 и IX.1
// внесены по советуемым вариантам двух вопросов (вопрос 1 — шаг нелинейной схемы назван на странице IX.4:
// стр. 34–36, знак сноски на стр. 147, новая сноска 10; вопрос 2 — «без изменения формы» в IX.1 уточнено
// условием nu = 1).
// Формализация — новые src/process/ProcessTransportProcess.v и src/process/ProcessBurgersStep.v; прежние файлы
// не менялись.
// Запуск: node patch-p09-step-02-pages.cjs  (затем relocate + merge по part09-ch04 и part09-ch01). Повторяем.
// Внимание: L() превращает знак «¤» в обратную косую черту.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 23.11 (Часть IX, шаг 2, слово автора)';
const KEPT = DONE + ' (формализацией; текст фразы не менялся): ';
const CL = 'Closed under the global context';
const TP = 'src/process/ProcessTransportProcess.v';
const BU = 'src/process/ProcessBurgersStep.v';
const BS = String.fromCharCode(92);
const L = (s) => s.split('¤').join(BS);   // «¤» — обратная косая черта
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
const N_MASS = 'transport_iter_mass : forall nu N (u : grid_fn) n, (0 < N)%nat -> sum_Q_ns (transport_iter nu N u n) N == sum_Q_ns u N (ProcessTransportProcess.v:108) — при любом nu и любом числе шагов. Периодичность посылкой не берётся: шаг использует только левого соседа, а он завёрнут в определении (ppred). ' + CL + '.';
const N_NN = 'transport_iter_nonneg : forall nu N, 0 <= nu -> nu <= 1 -> forall n (u : grid_fn), (forall k, 0 <= u k) -> forall j, 0 <= transport_iter nu N u n j (ProcessTransportProcess.v:121). ' + CL + '.';
const N_NNG = 'transport_iter_nonneg_grid : forall nu N, 0 <= nu -> nu <= 1 -> forall n (u : grid_fn), (forall k, (k < N)%nat -> 0 <= u k) -> forall j, (j < N)%nat -> 0 <= transport_iter nu N u n j (ProcessTransportProcess.v:161) — посылка и заключение только на узлах сетки. ' + CL + '.';
const N_BOXG = L('transport_iter_box_grid : forall nu N lo hi, 0 <= nu -> nu <= 1 -> forall n (u : grid_fn), in_box_grid N u lo hi -> in_box_grid N (transport_iter nu N u n) lo hi (ProcessTransportProcess.v:151); in_box_grid (:138) — границы только на узлах k < N. Различие двух посылок: off_grid_in_box_grid (:177), off_grid_not_in_box (:184). ') + CL + '.';
const N_IFF = L('transport_nonneg_iff_cfl : forall nu N, (2 <= N)%nat -> ((forall u : grid_fn, (forall k, 0 <= u k) -> forall j, (j < N)%nat -> 0 <= transport_step nu N u j) <-> (0 <= nu /¤ nu <= 1)) (ProcessTransportProcess.v:212); необходимость — transport_nonneg_needs_cfl (:198), свидетель — единичный импульс delta0 (:193). ') + CL + '.';
const N_UNST = L('transport_unstable_outside_cfl : forall nu N, (0 < N)%nat -> Nat.even N = true -> nu < 0 ¤/ 1 < nu -> forall B : Q, exists n, B < Qabs (transport_iter nu N transport_alt n 0%nat) (ProcessTransportProcess.v:309); transport_alt (:226) — профиль 1, −1, 1, −1, …; он собственный вектор шага с множителем 1 − 2 nu (alt_mode_step, :237; alt_mode_iter, :276; оценка роста alt_mode_growth, :294). ') + CL + '.';
const N_ZERO = 'transport_step_zero : forall N (u : grid_fn) j, transport_step 0 N u j == u j (ProcessTransportProcess.v:101). ' + CL + '.';
const N_SHIFT = 'transport_iter_shift : forall N (u : grid_fn) n k, transport_iter 1 N u n (n + k)%nat == u k (ProcessTransportProcess.v:476). ' + CL + '.';
const N_CYCLE = 'transport_full_cycle : forall N (u : grid_fn) k, (0 < N)%nat -> gperiodic N u -> transport_iter 1 N u N k == u k (ProcessTransportProcess.v:486); периодичность профиля шаг сохраняет — transport_step_gperiodic (:460), transport_iter_gperiodic (:467). ' + CL + '.';
const N_EN = 'transport_step_energy : forall nu N (u : grid_fn), (0 < N)%nat -> sum_Q_ns (fun j => transport_step nu N u j * transport_step nu N u j) N == sum_Q_ns (fun j => u j * u j) N - nu * (1 - nu) * sum_Q_ns (fun j => (u j - u (ppred N j)) * (u j - u (ppred N j))) N (ProcessTransportProcess.v:409) — равенство при любом nu; при 0 <= nu <= 1 сумма квадратов не растёт — transport_step_energy_le (:436). ' + CL + '.';
const N_ENF = 'transport_full_step_energy : forall N (u : grid_fn), (0 < N)%nat -> sum_Q_ns (fun j => transport_step 1 N u j * transport_step 1 N u j) N == sum_Q_ns (fun j => u j * u j) N (ProcessTransportProcess.v:451). ' + CL + '.';
const N_MONO = 'transport_iter_mono : forall nu N, 0 <= nu -> nu <= 1 -> forall n (u v : grid_fn), (forall k, u k <= v k) -> forall j, transport_iter nu N u n j <= transport_iter nu N v n j (ProcessTransportProcess.v:339); один шаг — transport_step_mono (:331). ' + CL + '.';
const N_STAB = 'transport_iter_stable : forall nu N eps, 0 <= nu -> nu <= 1 -> forall (u v : grid_fn), (forall k, Qabs (u k - v k) <= eps) -> forall n j, Qabs (transport_iter nu N u n j - transport_iter nu N v n j) <= eps (ProcessTransportProcess.v:375) — через линейность шага (transport_iter_diff, :362) и transport_iter_sup (:350). ' + CL + '.';
const N_L1 = 'transport_step_l1 : forall nu N (u : grid_fn), 0 <= nu -> nu <= 1 -> (0 < N)%nat -> sum_Q_ns (fun j => Qabs (transport_step nu N u j)) N <= sum_Q_ns (fun j => Qabs (u j)) N (ProcessTransportProcess.v:385). ' + CL + '.';
const N_HALF = L('p_prof_half_step : transport_step (1#2) 4 p_prof 0 == 5#2 /¤ transport_step (1#2) 4 p_prof 1 == 4 /¤ transport_step (1#2) 4 p_prof 2 == 3#2 /¤ transport_step (1#2) 4 p_prof 3 == 0 (ProcessTransportProcess.v:77); сумма 8 — p_prof_mass (:73). ') + CL + '.';
const N_FULL = L('p_prof_full_step : transport_step 1 4 p_prof 0 == 0 /¤ transport_step 1 4 p_prof 1 == 5 /¤ transport_step 1 4 p_prof 2 == 3 /¤ transport_step 1 4 p_prof 3 == 0 (ProcessTransportProcess.v:85). ') + CL + '.';
const N_CYC4 = L('p_prof_full_cycle : transport_iter 1 4 p_prof 4 0 == 5 /¤ transport_iter 1 4 p_prof 4 1 == 3 /¤ transport_iter 1 4 p_prof 4 2 == 0 /¤ transport_iter 1 4 p_prof 4 3 == 0 (ProcessTransportProcess.v:93). ') + CL + '.';
const N_NOST = 'transport_no_steepening : forall nu N (u : grid_fn) lo hi, 0 <= nu -> nu <= 1 -> in_box (bdiff N u) lo hi -> in_box (bdiff N (transport_step nu N u)) lo hi (ProcessTransportProcess.v:505); bdiff (:499) — разность соседних узлов u j − u (ppred N j); шаг и разность перестановочны — transport_step_bdiff (:501). ' + CL + '.';
const N_BDEF = 'Definition burgers_step (lam : Q) (N : nat) (u : grid_fn) : grid_fn := fun j => u j - lam * (1#2) * (u j * u j - u (ppred N j) * u (ppred N j)) (ProcessBurgersStep.v:50) — разность потоков u²/2 против потока; lam — отношение шагов Δt/Δx.';
const N_BLC = 'burgers_step_local_courant : forall lam N (u : grid_fn) j, burgers_step lam N u j == transport_step (lam * (1#2) * (u j + u (ppred N j))) N u j (ProcessBurgersStep.v:55). ' + CL + '.';
const N_BM = 'burgers_mass : forall lam N (u : grid_fn), (0 < N)%nat -> sum_Q_ns (burgers_step lam N u) N == sum_Q_ns u N (ProcessBurgersStep.v:61) — при любом lam. ' + CL + '.';
const N_BB = 'burgers_step_box : forall lam N (u : grid_fn) lo hi, 0 <= lam -> 0 <= lo -> lam * hi <= 1 -> in_box u lo hi -> in_box (burgers_step lam N u) lo hi (ProcessBurgersStep.v:80); hi — верхняя граница бокса (на странице — max u). ' + CL + '.';
const N_BST = L('burgers_steepens_concrete : bdiff 8 ramp8 2 == - (1#4) /¤ bdiff 8 (burgers_step 1 8 ramp8) 2 == - (5#16) /¤ sum_Q_ns (burgers_step 1 8 ramp8) 8 == sum_Q_ns ramp8 8 (ProcessBurgersStep.v:113); ramp8 (:102) — профиль 1, 3/4, 1/2, 1/4, 0, …, лежит в боксе [0, 1] (ramp8_in_box, :107). Одно вычисление, не общая теорема об укручении. ') + CL + '.';
const ALL45 = 'все 45 объявлений ProcessTransportProcess.v: Closed under the global context';
const ALL7 = 'все 7 объявлений ProcessBurgersStep.v: Closed under the global context';

// ================================================================ глава IX.4
{
  const { fix, add, save, claimOf } = open('part09-ch04');
  const C34 = 'Чего глава *не* делает: она не формализует ударные волны и слабые (энтропийные) решения *нелинейного* переноса (уравнения Бюргерса); о нелинейной схеме доказаны лишь свойства одного шага.';
  const C86 = L('При $¤nu=0$ (нет движения) профиль стоит.');
  const C88 = L('При промежуточных $¤nu$ профиль движется и слегка размывается (численная диффузия), но всегда остаётся выпуклым средним — отсюда все его свойства.');
  const F1 = 'Законы на всём процессе — `ProcessTransportProcess.v` (масса, неотрицательность и бокс на любом числе шагов, точность условия Куранта, сдвиг на $n$ узлов, баланс суммы квадратов; 40 утверждений, 0 аксиом).';
  const F2 = L('Что условие точное — `transport_nonneg_iff_cfl` (`ProcessTransportProcess.v`): при $N¤ge2$ неотрицательность для всякого неотрицательного профиля равносильна $0¤le¤nu¤le1$; вне условия значения знакопеременного профиля на сетке с чётным числом узлов превосходят любую границу (`transport_unstable_outside_cfl`). 0 аксиом.');
  const F3A = L('При $¤nu=0$ профиль стоит (`transport_step_zero`).');
  const F3B = L('За $n$ шагов при $¤nu=1$ профиль сдвигается на $n$ узлов (`transport_iter_shift`), а на периодической сетке за $N$ шагов возвращается на место (`transport_full_cycle`).');
  const F3C = L('Численная диффузия записана точным балансом: за шаг сумма квадратов убывает на $¤nu(1-¤nu)$, умноженное на сумму квадратов разностей соседних значений (`transport_step_energy`); при $¤nu=1$ она сохраняется. Все — `ProcessTransportProcess.v`, 0 аксиом.');
  const F4 = 'На всём процессе — `transport_iter_mass` (`ProcessTransportProcess.v`): сумма сохраняется при любом числе шагов.';
  const F5 = 'На всём процессе — `transport_iter_nonneg`; то же для профиля, заданного только на узлах сетки, — `transport_iter_nonneg_grid` (`ProcessTransportProcess.v`).';
  const F6A = 'На узлах сетки — `transport_iter_box_grid`.';
  const F6B = 'Следствия на всём процессе: принцип сравнения (`transport_iter_mono`) и устойчивость по начальным данным (`transport_iter_stable`); сумма модулей за шаг не растёт (`transport_step_l1`). Все — `ProcessTransportProcess.v`.';
  const F7 = 'Все четыре узла после полушага — $(5/2, 4, 3/2, 0)$ (`p_prof_half_step`, `ProcessTransportProcess.v`).';
  const F8 = 'Все четыре узла — $(0, 5, 3, 0)$ (`p_prof_full_step`); четыре полных шага возвращают профиль на место (`p_prof_full_cycle`).';
  const F10A = L('По эту сторону границы доказаны свойства одного шага консервативной схемы против потока для уравнения Бюргерса (`burgers_step`, `ProcessBurgersStep.v`): он есть шаг переноса с местным числом Куранта, зависящим от решения (`burgers_step_local_courant`); сохраняет массу (`burgers_mass`); удерживает неотрицательный профиль в его боксе, пока $¤lambda¤cdot¤max u¤le1$, где $¤lambda=¤Delta t/¤Delta x$ (`burgers_step_box`).');
  const F10B = 'На одном примере наклон спадающего участка растёт с $1/4$ до $5/16$ (`burgers_steepens_concrete`); линейный шаг разностей соседних узлов не увеличивает (`transport_no_steepening`).';
  const F10C = 'Ударные волны, слабые решения и поведение на многих шагах не формализованы. 0 аксиом.';

  // «Чего глава не делает» (вопрос 1, вариант 1)
  fix('Чего глава *не* делает: она не формализует *нелинейный* перенос', null, { claim: C34,
    note: DONE + ' (вопрос 1 шага 2, вариант 1): названо доказанное о нелинейной схеме. Ударных волн, слабых и энтропийных решений в формализации нет; об одном шаге схемы для уравнения Бюргерса — ProcessBurgersStep.v (5 Qed), см. сноску 10.' });
  add({ theorem: 'burgers_step', file: BU, claim: C34,
    note: '«О нелинейной схеме доказаны лишь свойства одного шага»: ' + N_BDEF + ' Свойства шага — burgers_step_local_courant (:55), burgers_mass (:61), burgers_step_box (:80); итерации шага в файле нет.' });

  // условие устойчивости и крайние случаи (сомнительные места первой вычитки)
  fix(L('Условие устойчивости $¤nu¤le1$ — это снова требование'), null, { theorem: 'transport_nonneg_iff_cfl', file: TP, assumptions: CL,
    note: KEPT + 'условие теперь доказано точным (при N >= 2): ' + N_IFF + ' Вне условия значения растут без границы: transport_unstable_outside_cfl (:309).' });
  add({ theorem: 'transport_step_zero', file: TP, assumptions: CL, claim: C86, note: KEPT + N_ZERO });
  add({ theorem: 'transport_step_energy', file: TP, assumptions: CL, claim: C88,
    note: KEPT + '«слегка размывается (численная диффузия)» записано точным балансом: ' + N_EN });

  // место 4.1: масса и неотрицательность на всём процессе
  fix(L('Полная масса $¤sum_j u_j$ не меняется со временем'), 'transport_mass', { theorem: 'transport_iter_mass', file: TP, assumptions: CL,
    note: KEPT + '«не меняется со временем» теперь доказано на всём процессе: ' + N_MASS + ' Прежняя лемма одного шага — transport_mass (ProcessTransport.v).' });
  fix('*Неотрицательность*: если профиль всюду неотрицателен', 'transport_step_nonneg', { theorem: 'transport_iter_nonneg', file: TP, assumptions: CL,
    note: KEPT + '«он таким и останется» теперь доказано на всём процессе: ' + N_NN + ' Прежняя лемма одного шага — transport_step_nonneg (ProcessTransport.v).' });

  // сноска 1
  add({ theorem: null, file: TP, claim: F1, page_price: '0 аксиом', assumptions: ALL45,
    note: DONE + ': новый опорный файл в сноске. src/process/ProcessTransportProcess.v: 40 Qed и пять определений; строк Axiom, Parameter, Admitted нет.' });

  // сноска 2
  add({ theorem: 'transport_nonneg_iff_cfl', file: TP, assumptions: CL, claim: F2, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_IFF });
  add({ theorem: 'transport_unstable_outside_cfl', file: TP, assumptions: CL, claim: F2, page_price: '0 аксиом', note: N_UNST });

  // сноска 3
  add({ theorem: 'transport_step_zero', file: TP, assumptions: CL, claim: F3A, note: DONE + ': новая фраза. ' + N_ZERO });
  add({ theorem: 'transport_iter_shift', file: TP, assumptions: CL, claim: F3B, note: DONE + ': новая фраза. ' + N_SHIFT });
  add({ theorem: 'transport_full_cycle', file: TP, assumptions: CL, claim: F3B, note: N_CYCLE });
  add({ theorem: 'transport_step_energy', file: TP, assumptions: CL, claim: F3C, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_EN });
  add({ theorem: 'transport_full_step_energy', file: TP, assumptions: CL, claim: F3C, page_price: '0 аксиом', note: L('«При $¤nu=1$ она сохраняется»: ') + N_ENF });

  // сноски 4 и 5 (место 4.1)
  add({ theorem: 'transport_iter_mass', file: TP, assumptions: CL, claim: F4, note: DONE + ': новая фраза. ' + N_MASS });
  add({ theorem: 'transport_iter_nonneg', file: TP, assumptions: CL, claim: F5, note: DONE + ': новая фраза. ' + N_NN });
  add({ theorem: 'transport_iter_nonneg_grid', file: TP, assumptions: CL, claim: F5, note: N_NNG });

  // сноска 6
  add({ theorem: 'transport_iter_box_grid', file: TP, assumptions: CL, claim: F6A, note: DONE + ': новая фраза. ' + N_BOXG });
  add({ theorem: 'transport_iter_mono', file: TP, assumptions: CL, claim: F6B, note: DONE + ': новая фраза. ' + N_MONO });
  add({ theorem: 'transport_iter_stable', file: TP, assumptions: CL, claim: F6B, note: N_STAB });
  add({ theorem: 'transport_step_l1', file: TP, assumptions: CL, claim: F6B, note: N_L1 });

  // сноски 7 и 8
  add({ theorem: 'p_prof_half_step', file: TP, assumptions: CL, claim: F7, note: DONE + ': новая фраза. ' + N_HALF });
  add({ theorem: 'p_prof_full_step', file: TP, assumptions: CL, claim: F8, note: DONE + ': новая фраза. ' + N_FULL });
  add({ theorem: 'p_prof_full_cycle', file: TP, assumptions: CL, claim: F8, note: N_CYC4 });

  // сноска 10 (вопрос 1, вариант 1)
  add({ theorem: 'burgers_step', file: BU, claim: F10A, note: DONE + ' (вопрос 1 шага 2, вариант 1): новая сноска. ' + N_BDEF });
  add({ theorem: 'burgers_step_local_courant', file: BU, assumptions: CL, claim: F10A, note: N_BLC });
  add({ theorem: 'burgers_mass', file: BU, assumptions: CL, claim: F10A, note: N_BM });
  add({ theorem: 'burgers_step_box', file: BU, assumptions: CL, claim: F10A, note: N_BB });
  add({ theorem: 'burgers_steepens_concrete', file: BU, assumptions: CL, claim: F10B, note: N_BST });
  add({ theorem: 'transport_no_steepening', file: TP, assumptions: CL, claim: F10B, note: N_NOST });
  add({ theorem: null, file: BU, claim: F10C, page_price: '0 аксиом', assumptions: ALL7,
    note: 'src/process/ProcessBurgersStep.v: 5 Qed и два определения; строк Axiom, Parameter, Admitted нет. Итерации шага, ударных волн, слабых и энтропийных решений в файле нет.' });

  save();
}

// ================================================================ глава IX.1
{
  const { fix, add, save } = open('part09-ch01');
  const C171 = L('Пространственный оператор — первая производная; процесс *движет* профиль — при числе Куранта $¤nu=1$ без изменения формы, при меньшем слегка размывая его. Роль оператора — *сохранение*: полная масса не меняется.');

  // перенос в триптихе (вопрос 2, вариант 1)
  fix('Пространственный оператор — первая производная; процесс *движет* профиль без', 'transport_mass', { claim: C171, theorem: 'transport_iter_mass', file: TP, assumptions: CL,
    note: DONE + ' (вопрос 2 шага 2, вариант 1): «без изменения формы» уточнено условием на число Куранта. «Полная масса не меняется» — на всём процессе: ' + N_MASS });
  add({ theorem: 'transport_iter_shift', file: TP, assumptions: CL, claim: C171, note: L('«При числе Куранта $¤nu=1$ без изменения формы»: ') + N_SHIFT });
  add({ theorem: 'transport_step_energy', file: TP, assumptions: CL, claim: C171, note: '«При меньшем слегка размывая его»: ' + N_EN });

  save();
}
