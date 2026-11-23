// Часть IX, шаг 1, страницы (2026-11-23, слово автора «Делай»): 13 правок глав IX.1 и IX.2 внесены
// (советуемые варианты двух вопросов: запись grid-функции в Elements приведена к типу ℕ → ℚ; фраза о
// периодичности как свойстве профиля добавлена в основной текст IX.2).
// Формализация — новые src/process/ProcessPeriodicGrid.v и src/process/ProcessHeatProcess.v; прежние файлы
// не менялись.
// Запуск: node patch-p09-step-01-pages.cjs  (затем relocate + merge по part09-ch01 и part09-ch02). Повторяем.
// Внимание: L() превращает знак «¤» в обратную косую черту.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 23.11 (Часть IX, шаг 1, слово автора)';
const KEPT = DONE + ' (формализацией; текст фразы не менялся): ';
const CL = 'Closed under the global context';
const PG = 'src/process/ProcessPeriodicGrid.v';
const HP = 'src/process/ProcessHeatProcess.v';
const HE = 'src/process/ProcessHeatEquation.v';
const GR = 'src/process/ProcessPDEGreen.v';
const GF = 'src/navier_stokes/GridFunction.v';
const FD = 'src/navier_stokes/FiniteDifference.v';
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
const N_GP = 'Definition gperiodic (N : nat) (u : grid_fn) : Prop := forall j, u (j + N)%nat == u j (ProcessPeriodicGrid.v:60) — периодичность как свойство профиля. Следствия: u N == u 0 (gperiodic_N0, :63), u (S N) == u 1 (gperiodic_SN, :66), u j == u (j mod N) (gperiodic_mod, :82); периодическое продолжение всякого профиля — pext (:94), pext_gperiodic (:96).';
const N_GG = 'gperiodic_green : forall N (u : grid_fn), gperiodic N u -> sum_Q_ns (fun i => u (S i) * dd u i) N == - gradient_norm_sq N u (ProcessPeriodicGrid.v:172). ' + CL + '.';
const N_GL = 'gperiodic_lap_bound : forall N (u : grid_fn), gperiodic N u -> gf_norm_sq N (dd u) <= 4 * gradient_norm_sq N u (ProcessPeriodicGrid.v:180). ' + CL + '.';
const N_GB = 'green_boundary : forall N (u : grid_fn), sum_Q_ns (fun i => u (S i) * dd u i) N == - gradient_norm_sq N u + (u N * fd u N - u 0 * fd u 0) (ProcessPeriodicGrid.v:194) — без условий на края. ' + CL + '.';
const N_GZ = 'green_zero_boundary : forall N (u : grid_fn), u 0 == 0 -> u N == 0 -> sum_Q_ns (fun i => u (S i) * dd u i) N == - gradient_norm_sq N u (ProcessPeriodicGrid.v:207). ' + CL + '.';
const N_LB = 'lap_norm_bound_boundary : forall N (u : grid_fn), gf_norm_sq N (dd u) <= 4 * gradient_norm_sq N u + 2 * (fd u N * fd u N - fd u 0 * fd u 0) (ProcessPeriodicGrid.v:218) — без условий на края. ' + CL + '.';
const N_LN = 'lap_bound_not_unconditional : ~ (forall N (u : grid_fn), gf_norm_sq N (dd u) <= 4 * gradient_norm_sq N u) (ProcessPeriodicGrid.v:246); свидетель — cex_lap при N = 1. Одного равенства u N == u 0 мало и для формулы Грина: green_not_from_is_periodic (:264). ' + CL + '.';
const N_LS = 'lap_bound_sharp : gf_norm_sq 2 (dd zigzag) == 4 * gradient_norm_sq 2 zigzag (ProcessPeriodicGrid.v:281); zigzag — профиль 0,1,0,1,…, периодический с периодом 2 (zigzag_gperiodic, :275). ' + CL + '.';
const N_HSG = 'heat_step_gperiodic : forall r N u, (0 < N)%nat -> gperiodic N u -> gperiodic N (heat_step r N u) (ProcessHeatProcess.v:113); на всём процессе — heat_iter_gperiodic (:122). ' + CL + '.';
const N_HES = 'heat_iter_energy_step : forall r N u n, 0 <= r -> 2*r <= 1 -> (0 < N)%nat -> gperiodic N u -> gf_norm_sq N (heat_iter r N u (S n)) <= gf_norm_sq N (heat_iter r N u n) (ProcessHeatProcess.v:131) — на каждом шаге; между любыми двумя шагами — heat_iter_energy_mono (:140). ' + CL + '.';
const N_HIE = 'heat_iter_energy : forall r N u n, 0 <= r -> 2*r <= 1 -> (0 < N)%nat -> gperiodic N u -> gf_norm_sq N (heat_iter r N u n) <= gf_norm_sq N u (ProcessHeatProcess.v:149). ' + CL + '.';
const N_HIM = 'heat_iter_mass : forall r N u n, (0 < N)%nat -> gperiodic N u -> sum_Q_ns (heat_iter r N u n) N == sum_Q_ns u N (ProcessHeatProcess.v:184) — при любом r; один шаг — heat_step_mass (:162). ' + CL + '.';
const N_PNP = 'premise_not_preserved : ~ (heat_step (1#4) 2 u_bad 2 == heat_step (1#4) 2 u_bad 0) (ProcessHeatProcess.v:83); u_bad — профиль 1, 0, 1, 100, 0, … (посылка u 2 == u 0 выполнена). ' + CL + '.';
const N_ETF = 'energy_two_steps_fails : exists (r : Q) (N : nat) (u : grid_fn), 0 <= r ' + AND + ' 2*r <= 1 ' + AND + ' (0 < N)%nat ' + AND + ' u N == u 0 ' + AND + ' gf_norm_sq N u < gf_norm_sq N (heat_iter r N u 2) (ProcessHeatProcess.v:95); значения энергии 1, 1/2, 733/16 — u_bad_energies (:88). ' + CL + '.';
const N_BOX = 'heat_box_iff : forall r N, (forall (u : grid_fn) lo hi, in_box u lo hi -> in_box (heat_step r N u) lo hi) <-> (0 <= r ' + AND + ' 2*r <= 1) (ProcessHeatProcess.v:222). ' + CL + '.';
const N_ALT = 'heat_alt_energy_grows : forall r, 1 < 2*r -> gf_norm_sq 2 heat_alt < gf_norm_sq 2 (heat_step r 2 heat_alt) (ProcessHeatProcess.v:255); heat_alt — профиль 1, −1, 1, −1, …, периодический с периодом 2 (heat_alt_gperiodic, :238). ' + CL + '.';
const N_HALF = 'heat_alt_energy_conserved_half : gf_norm_sq 2 (heat_step (1#2) 2 heat_alt) == gf_norm_sq 2 heat_alt (ProcessHeatProcess.v:264). ' + CL + '.';
const N_BAL = 'heat_energy_balance : forall r N (u : grid_fn), (0 < N)%nat -> u N == u 0 -> gf_norm_sq N (heat_step r N u) + sum_Q_ns (heat_diss r N u) N == gf_norm_sq N u (ProcessHeatProcess.v:293); heat_diss (:274) — сумма трёх квадратов разностей соседних значений с весами r(1−2r), r², (1−2r)r; неотрицательна при 0 <= r <= 1/2 (heat_diss_nonneg, :279). На каждом шаге процесса — heat_iter_energy_balance (:319). ' + CL + '.';
const N_STR = 'heat_energy_strict : forall r N (u : grid_fn) k, 0 < r -> 2*r < 1 -> (0 < N)%nat -> u N == u 0 -> (k < N)%nat -> ~ u k == u (S k) -> gf_norm_sq N (heat_step r N u) < gf_norm_sq N u (ProcessHeatProcess.v:352). ' + CL + '.';
const N_EUL = 'heat_step_euler_form : forall r N (u : grid_fn) j, heat_step r N u j == u j + r * (u (S j) - 2 * u j + u (ppred N j)) (ProcessHeatProcess.v:381). ' + CL + '.';
const N_HDD = 'heat_step_dd : forall r N (u : grid_fn) k, heat_step r N u (S k) == u (S k) + r * dd u k (ProcessHeatProcess.v:386). ' + CL + '.';
const N_STB = 'heat_iter_stable : forall r N (u v : grid_fn) d n, 0 <= r -> 2*r <= 1 -> (forall k, Qabs (u k - v k) <= d) -> forall k, Qabs (heat_iter r N u n k - heat_iter r N v n k) <= d (ProcessHeatProcess.v:410) — следствие линейности шага и heat_iter_box. ' + CL + '.';
const N_IMP = 'heat_impulse_profile : heat_step (1#4) 4 u_imp 0 == 1#2 ' + AND + ' heat_step (1#4) 4 u_imp 1 == 1#4 ' + AND + ' heat_step (1#4) 4 u_imp 2 == 0 ' + AND + ' heat_step (1#4) 4 u_imp 3 == 1#4 (ProcessHeatProcess.v:428). ' + CL + '.';
const N_PIMP = 'pext_impulse_profile (ProcessHeatProcess.v:459): те же четыре значения для периодически продолженного импульса pext 4 u_imp; энергия после шага 3/8 — pext_impulse_energy (:466). Сама u_imp не периодична (u_imp_not_gperiodic, :440): её посылка u 4 == u 0 теряется на шаге 4 (imp_premise_lost_step4, :445), и на шаге 5 сумма уже 1023/1024 (imp_mass_leaks_step5, :450). ' + CL + '.';
const ALL32 = 'все 32 объявления ProcessPeriodicGrid.v: Closed under the global context';
const ALL47 = 'все 47 объявлений ProcessHeatProcess.v: Closed under the global context';

// ================================================================ глава IX.1
{
  const { fix, add, save, claimOf } = open('part09-ch01');
  const C78 = L('Grid-функции $u^n:ℕ¤toℚ$ (на периодической сетке — с периодом $N$: их задают значения в узлах $0,…,N{-}1$), рациональные значения в узлах $u^n_j$, конечная пространственная сетка, конечный номер шага.');
  const C144 = L('и, при том же условии, сопутствующая оценка $¤norm{¤Delta_h u}^2 ¤le 4 ¤norm{¤nabla_h u}^2$.[^4] Эти тождества — конечные суммы над ℚ;');
  const C217 = L('grid-функции $u^n:ℕ¤toℚ$ (на периодической сетке — с периодом $N$), значения в узлах $u^n_j¤inℚ$, конечные суммы $¤sum_{j<N}$, конечная сетка и конечный номер шага.');
  const F1A = L('Опорная инфраструктура — `GridFunction.v` и `FiniteDifference.v` (каталог `navier_stokes/` Rocq-репозитория ToS; grid-функции, суммы, нормы, `fd`, `dd`, суммирование по частям `abel_summation`; 84 доказанных утверждения — 43 и 41, 0 аксиом)');
  const F1B = L('плюс новый файл `ProcessPDEGreen.v` (`process/`: дискретная формула Грина и оценка $¤norm{¤Delta u}^2¤le 4¤norm{¤nabla u}^2$; 8 утверждений, 0 аксиом, `Print Assumptions`: «closed under the global context»)');
  const F1C = 'и `ProcessPeriodicGrid.v` (там же: периодичность как свойство профиля, формула Грина и оценка лапласиана с граничными членами; 27 утверждений, 0 аксиом).';
  const F4A = L('`green_dirichlet_periodic` и `lap_norm_bound` в `ProcessPDEGreen.v` (новый файл Части IX, проверено `Print Assumptions`: «closed under the global context»), 0 аксиом — для прямого лапласиана; посылки — $u_N=u_0$, $u_{N+1}=u_1$ у тождества и $(¤nabla_h u)_N=(¤nabla_h u)_0$ у оценки.');
  const F4B = 'Периодичность как свойство профиля — $u_{j+N}=u_j$ при всех $j$ (`gperiodic`, `ProcessPeriodicGrid.v`); из неё следуют обе посылки (`gperiodic_green`, `gperiodic_lap_bound`).';
  const F4C = 'Для всякой grid-функции тождество и оценка верны с граничными членами (`green_boundary`, `lap_norm_bound_boundary`), при нулевых значениях на краях тождество — `green_zero_boundary`; без условия на края оценка неверна (`lap_bound_not_unconditional`), а постоянная 4 достигается (`lap_bound_sharp`). 0 аксиом.';

  // каркас и разбор (вопрос 1)
  fix(L('Grid-функции $u^n:¤{0,…,N{-}1¤}¤toℚ$, рациональные'), null, { claim: C78,
    note: DONE + ' (вопрос 1 шага 1, вариант 1): запись приведена к типу формализации. Definition grid_fn := nat -> Q (GridFunction.v:132); число узлов N входит верхним пределом сумм и периодом. ' + N_GP });
  add({ theorem: 'gperiodic', file: PG, claim: C217,
    note: DONE + ' (вопрос 1 шага 1, вариант 1): запись в разборе приведена к типу формализации. ' + N_GP });

  // оценка лапласиана
  fix('суммирование по частям (формула Абеля) и дискретная формула Грина', null, {
    note: 'abel_summation (FiniteDifference.v:170) — без условий на края; green_dirichlet_periodic (ProcessPDEGreen.v:87) — при u N == u 0 и u (S N) == u 1; lap_norm_bound (:123) — при fd u N == fd u 0. В этой сводной фразе условия не названы; с шага 1 Части IX они названы на стр. 141–144 и в сноске 4, а без условий обе формулы даны с граничными членами (green_boundary, lap_norm_bound_boundary, ProcessPeriodicGrid.v:194, :218).' });
  fix('и сопутствующая оценка', 'lap_norm_bound', { claim: C144, assumptions: CL,
    note: DONE + ': названо условие («при том же условии»). Lemma lap_norm_bound : forall N (u : grid_fn), fd u N == fd u 0 -> gf_norm_sq N (dd u) <= 4 * gradient_norm_sq N u (ProcessPDEGreen.v:123). Без посылки оценка неверна (lap_bound_not_unconditional, ProcessPeriodicGrid.v:246); при периодичности профиля — gperiodic_lap_bound (:180). ' + CL + '.' });
  add({ theorem: 'gperiodic_lap_bound', file: PG, assumptions: CL, claim: C144, note: '«При том же условии» — на периодической сетке: ' + N_GL });

  // триптих и анонс: энергия тепла на всём процессе
  add({ theorem: 'heat_iter_energy', file: HP, assumptions: CL, claim: claimOf('Пространственный оператор — лапласиан; процесс *сглаживает*'),
    note: KEPT + '«энергия убывает» теперь доказано на всём процессе (неравенство нестрогое): ' + N_HIE });
  add({ theorem: 'heat_iter_energy', file: HP, assumptions: CL, claim: claimOf('Следующая глава предъявляет первый и канонический процесс'),
    note: KEPT + '«с доказанным принципом максимума и диссипацией энергии»: ' + N_HIE });

  // сноска 1 (место 1.1)
  fix('Опорная инфраструктура — `GridFunction.v` и `FiniteDifference.v`', null, { claim: F1A,
    note: DONE + ': число исправлено. Счёт Qed: GridFunction.v — 43, FiniteDifference.v — 41, вместе 84. Каталог и состав названы верно; цена верна: все 100 объявлений двух файлов — Closed under the global context.' });
  fix('плюс новый файл `ProcessPDEGreen.v`', null, { claim: F1B });
  add({ theorem: null, file: PG, claim: F1C, page_price: '0 аксиом', assumptions: ALL32,
    note: DONE + ': новый опорный файл в сноске. src/process/ProcessPeriodicGrid.v: 27 Qed и пять определений; строк Axiom, Parameter, Admitted нет.' });

  // сноска 4
  fix('`green_dirichlet_periodic` и `lap_norm_bound` в `ProcessPDEGreen.v`', 'green_dirichlet_periodic', { claim: F4A, assumptions: CL, page_price: '0 аксиом',
    note: DONE + ': названы посылки. Lemma green_dirichlet_periodic : forall N (u : grid_fn), u N == u 0 -> u (S N) == u 1 -> sum_Q_ns (fun i => u (S i) * dd u i) N == - gradient_norm_sq N u (ProcessPDEGreen.v:87); lap_norm_bound (:123) — при fd u N == fd u 0. ' + CL + '.' });
  add({ theorem: 'lap_norm_bound', file: GR, assumptions: CL, claim: F4A, page_price: '0 аксиом',
    note: 'Lemma lap_norm_bound : forall N (u : grid_fn), fd u N == fd u 0 -> gf_norm_sq N (dd u) <= 4 * gradient_norm_sq N u (ProcessPDEGreen.v:123). ' + CL + '.' });
  add({ theorem: 'gperiodic', file: PG, claim: F4B, note: DONE + ': новая фраза. ' + N_GP });
  add({ theorem: 'gperiodic_green', file: PG, assumptions: CL, claim: F4B, note: N_GG });
  add({ theorem: 'gperiodic_lap_bound', file: PG, assumptions: CL, claim: F4B, note: N_GL });
  add({ theorem: 'green_boundary', file: PG, assumptions: CL, claim: F4C, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_GB });
  add({ theorem: 'lap_norm_bound_boundary', file: PG, assumptions: CL, claim: F4C, page_price: '0 аксиом', note: N_LB });
  add({ theorem: 'green_zero_boundary', file: PG, assumptions: CL, claim: F4C, page_price: '0 аксиом', note: N_GZ });
  add({ theorem: 'lap_bound_not_unconditional', file: PG, assumptions: CL, claim: F4C, page_price: '0 аксиом', note: N_LN });
  add({ theorem: 'lap_bound_sharp', file: PG, assumptions: CL, claim: F4C, page_price: '0 аксиом', note: N_LS });

  save();
}

// ================================================================ глава IX.2
{
  const { fix, add, save, claimOf } = open('part09-ch02');
  const C32 = L('при $0¤le r¤le ¤tfrac12$ доказан *принцип максимума* (значения не выходят за начальные пределы) и *диссипация энергии* (на периодической сетке норма не растёт ни на одном шаге), а сглаживание импульса вычислено точно.[^1]');
  const C145 = 'Периодичность здесь — свойство самого профиля, $u_{j+N}=u_j$ при всех $j$: шаг схемы её сохраняет, и потому оценка действует на каждом шаге, на всём процессе.';
  const G1 = 'Законы на всём процессе — `ProcessHeatProcess.v` (сохранение периодичности шагом, энергия и сумма значений на всём процессе, точность условия на $r$; 42 утверждения, 0 аксиом); периодичность как свойство профиля — `ProcessPeriodicGrid.v` (27 утверждений, 0 аксиом).';
  const G2A = 'Правый сосед — узел $j+1$; сетку замыкает периодичность профиля, $u_{j+N}=u_j$ (`gperiodic`, `ProcessPeriodicGrid.v`).';
  const G2B = 'Запись шага через центрированную разность — `heat_step_euler_form`; во внутренних узлах она есть `dd` со сдвигом номера — `heat_step_dd` (`ProcessHeatProcess.v`).';
  const G3 = L('Что условие точное — `heat_box_iff` (`ProcessHeatProcess.v`): принцип максимума для всякого профиля равносилен $0¤le r¤le¤tfrac12$; при $r>¤tfrac12$ энергия знакопеременного профиля растёт (`heat_alt_energy_grows`). 0 аксиом.');
  const G5 = 'Следствие — устойчивость по начальным данным: два процесса, начальные профили которых различаются не больше чем на $d$ в каждом узле, различаются не больше чем на $d$ на каждом шаге (`heat_iter_stable`, `ProcessHeatProcess.v`).';
  const G6A = 'Лемма говорит об одном шаге и берёт посылкой равенство $u_N=u_0$; одного его недостаточно: шаг это равенство не сохраняет, и есть профиль, у которого энергия на втором шаге растёт (`premise_not_preserved`, `energy_two_steps_fails`).';
  const G6B = 'При периодичности профиля шаг её сохраняет (`heat_step_gperiodic`), и энергия не растёт на каждом шаге и на всём процессе (`heat_iter_energy_step`, `heat_iter_energy`), а сумма значений («масса») сохраняется (`heat_iter_mass`).';
  const G6C = L('Точный баланс: энергия после шага и поузельная диссипация в сумме равны энергии до шага (`heat_energy_balance`); при $0<r<¤tfrac12$ и непостоянном профиле убывание строгое (`heat_energy_strict`), при $r=¤tfrac12$ энергия может сохраниться (`heat_alt_energy_conserved_half`). Все — `ProcessHeatProcess.v`, 0 аксиом.');
  const G7 = 'Все четыре узла — `heat_impulse_profile` (`ProcessHeatProcess.v`). Функция `u_imp` равна единице в узлах 0 и 4 и нулю в прочих; импульс, продолженный периодически (`pext`), на первом шаге даёт тот же профиль (`pext_impulse_profile`).';
  const PFX32 = L('при $0¤le r¤le ¤tfrac12$ доказан *принцип максимума*');

  // «Что эта глава утверждает» (место 2.1)
  fix(PFX32, 'heat_iter_box', { claim: C32, assumptions: CL });
  fix(PFX32, 'heat_step_energy', { theorem: 'heat_iter_energy_step', file: HP, claim: C32, assumptions: CL,
    note: DONE + ': названа периодическая сетка и «ни на одном шаге». ' + N_HES + ' Прежняя лемма одного шага — heat_step_energy (ProcessHeatEquation.v:124), при u N == u 0.' });

  // условие устойчивости «в точности»
  fix(L('Условие устойчивости $r¤le¤tfrac12$ есть в точности'), null, { theorem: 'heat_box_iff', file: HP, assumptions: CL,
    note: KEPT + '«в точности» теперь теорема (при r >= 0): ' + N_BOX + ' Вне условия энергия может расти: heat_alt_energy_grows (:255).' });

  // диссипация энергии (место 2.1)
  add({ theorem: 'heat_iter_mass', file: HP, assumptions: CL, claim: claimOf('Под энергией здесь понимаем дискретную'),
    note: KEPT + '«при сохранённой массе» — закон сохранения суммы записан: ' + N_HIM });
  fix('Энергия диссипирует: с каждым шагом профиль становится более', 'heat_step_energy', { theorem: 'heat_iter_energy_step', file: HP, assumptions: CL,
    note: KEPT + '«с каждым шагом» теперь доказано на периодической сетке: ' + N_HES + ' Одной посылки u N == u 0 для этого мало: energy_two_steps_fails (:95).' });
  add({ theorem: 'heat_step_gperiodic', file: HP, assumptions: CL, claim: C145,
    note: DONE + ' (вопрос 2 шага 1, вариант 1): новая фраза. «Шаг схемы её сохраняет»: ' + N_HSG });
  add({ theorem: 'heat_iter_energy', file: HP, assumptions: CL, claim: C145, note: '«Оценка действует на каждом шаге, на всём процессе»: ' + N_HIE });
  add({ theorem: 'gperiodic', file: PG, claim: C145, note: '«Свойство самого профиля»: ' + N_GP });

  // импульс (место 2.2)
  fix('Пик оседает с $1$ до', 'heat_peak_drops', { theorem: 'heat_impulse_profile', file: HP, assumptions: CL,
    note: KEPT + 'все четыре значения профиля записаны одной леммой: ' + N_IMP + ' Прежняя heat_peak_drops (ProcessHeatEquation.v:157) даёт значение узла 0.' });

  // сноска 1
  add({ theorem: null, file: HP, claim: G1, page_price: '0 аксиом', assumptions: ALL47,
    note: DONE + ': новый опорный файл в сноске. src/process/ProcessHeatProcess.v: 42 Qed и пять определений; строк Axiom, Parameter, Admitted нет.' });
  add({ theorem: null, file: PG, claim: G1, page_price: '0 аксиом', assumptions: ALL32,
    note: 'src/process/ProcessPeriodicGrid.v: 27 Qed и пять определений; строк Axiom, Parameter, Admitted нет.' });

  // сноска 2
  add({ theorem: 'gperiodic', file: PG, claim: G2A,
    note: DONE + ': новая фраза. В heat_step правый сосед — u (S j), левый — u (ppred N j) (ProcessHeatEquation.v:46–47); сетку замыкает свойство профиля. ' + N_GP });
  add({ theorem: 'heat_step_euler_form', file: HP, assumptions: CL, claim: G2B, note: DONE + ': новая фраза. ' + N_EUL });
  add({ theorem: 'heat_step_dd', file: HP, assumptions: CL, claim: G2B, note: N_HDD });
  add({ theorem: 'dd', file: FD, claim: G2B, note: 'Definition dd (FiniteDifference.v:75): f (S (S i)) - 2 * f (S i) + f i — повторная прямая разность.' });

  // сноска 3
  add({ theorem: 'heat_box_iff', file: HP, assumptions: CL, claim: G3, page_price: '0 аксиом', note: DONE + ': новая фраза. ' + N_BOX });
  add({ theorem: 'heat_alt_energy_grows', file: HP, assumptions: CL, claim: G3, page_price: '0 аксиом', note: N_ALT });

  // сноска 5
  add({ theorem: 'heat_iter_stable', file: HP, assumptions: CL, claim: G5, note: DONE + ': новая фраза. ' + N_STB });

  // сноска 6 (место 2.1)
  add({ theorem: 'premise_not_preserved', file: HP, assumptions: CL, claim: G6A, note: DONE + ': новая фраза. ' + N_PNP });
  add({ theorem: 'energy_two_steps_fails', file: HP, assumptions: CL, claim: G6A, note: N_ETF });
  add({ theorem: 'heat_step_gperiodic', file: HP, assumptions: CL, claim: G6B, note: N_HSG });
  add({ theorem: 'heat_iter_energy_step', file: HP, assumptions: CL, claim: G6B, note: N_HES });
  add({ theorem: 'heat_iter_energy', file: HP, assumptions: CL, claim: G6B, note: N_HIE });
  add({ theorem: 'heat_iter_mass', file: HP, assumptions: CL, claim: G6B, note: N_HIM });
  add({ theorem: 'heat_energy_balance', file: HP, assumptions: CL, claim: G6C, page_price: '0 аксиом', note: N_BAL });
  add({ theorem: 'heat_energy_strict', file: HP, assumptions: CL, claim: G6C, page_price: '0 аксиом', note: N_STR });
  add({ theorem: 'heat_alt_energy_conserved_half', file: HP, assumptions: CL, claim: G6C, page_price: '0 аксиом', note: N_HALF });

  // сноска 7 (место 2.2)
  add({ theorem: 'heat_impulse_profile', file: HP, assumptions: CL, claim: G7, note: DONE + ': новая фраза. ' + N_IMP });
  add({ theorem: 'u_imp', file: HE, claim: G7,
    note: 'Definition u_imp : grid_fn := fun j => match j with O => 1 | S (S (S (S O))) => 1 | _ => 0 end (ProcessHeatEquation.v:153) — единица в узлах 0 и 4.' });
  add({ theorem: 'pext', file: PG, claim: G7,
    note: 'Definition pext (N : nat) (u : grid_fn) : grid_fn := fun j => u (j mod N)%nat (ProcessPeriodicGrid.v:94) — периодическое продолжение; pext_gperiodic (:96), pext_agrees (:104).' });
  add({ theorem: 'pext_impulse_profile', file: HP, assumptions: CL, claim: G7, note: N_PIMP });

  save();
}
