// Часть IX, шаг 3, страницы (2026-11-23, слово автора «Делай»): 18 правок главы IX.3 внесены по советуемым
// вариантам двух вопросов (вопрос 1 — текст об энергии принят целиком, включая курсив раздела «Энергия и
// граница»; вопрос 2 — данные примера названы «прошлый уровень нулевой», числа оставлены).
// Формализация — новые src/process/ProcessWaveProcess.v и src/process/ProcessWaveConservation.v; прежние файлы
// не менялись.
// Запуск: node patch-p09-step-03-pages.cjs  (затем relocate + merge по part09-ch03 и part09-ch01). Повторяем.
// Внимание: L() превращает знак «¤» в обратную косую черту.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 23.11 (Часть IX, шаг 3, слово автора)';
const KEPT = DONE + ' (формализацией; текст фразы не менялся): ';
const CL = 'Closed under the global context';
const WP = 'src/process/ProcessWaveProcess.v';
const WC = 'src/process/ProcessWaveConservation.v';
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
const N_ITER = 'Fixpoint wave_iter (s : Q) (N : nat) (u0 u1 : grid_fn) (n : nat) : grid_fn * grid_fn (ProcessWaveProcess.v:128) — пара (прошлый уровень, текущий уровень) после n шагов.';
const N_FS = L('wave_finite_speed_n : forall s N (u0 u1 : grid_fn) a b, (forall k, (a <= k <= b)%nat -> u0 k == 0) -> (forall k, (a <= k <= b)%nat -> u1 k == 0) -> forall n j, (a + n <= j)%nat -> (j + n <= b)%nat -> fst (wave_iter s N u0 u1 n) j == 0 /¤ snd (wave_iter s N u0 u1 n) j == 0 (ProcessWaveProcess.v:154) — при всяком s и всяком N; узел с тихой окрестностью радиуса n молчит n шагов — wave_quiet_n (:172). ') + CL + '.';
const N_CONE = L('wave_dependence_cone_n : forall s N (u0 u1 v0 v1 : grid_fn) a b, (forall k, (a <= k <= b)%nat -> u0 k == v0 k) -> (forall k, (a <= k <= b)%nat -> u1 k == v1 k) -> forall n j, (a + n <= j)%nat -> (j + n <= b)%nat -> fst (wave_iter s N u0 u1 n) j == fst (wave_iter s N v0 v1 n) j /¤ snd (wave_iter s N u0 u1 n) j == snd (wave_iter s N v0 v1 n) j (ProcessWaveProcess.v:183). ') + CL + '.';
const N_VCONE = 'wave_value_depends_on_cone : forall s N (u0 u1 v0 v1 : grid_fn) n j, (n <= j)%nat -> (forall k, (j - n <= k <= j + n)%nat -> u0 k == v0 k) -> (forall k, (j - n <= k <= j + n)%nat -> u1 k == v1 k) -> snd (wave_iter s N u0 u1 n) j == snd (wave_iter s N v0 v1 n) j (ProcessWaveProcess.v:204). ' + CL + '.';
const N_TWO = L('wave_two_steps_reach : snd (wave_iter (1#2) 7 wzero wimp3 2) 1 == 1#4 /¤ snd (wave_iter (1#2) 7 wzero wimp3 2) 0 == 0 (ProcessWaveProcess.v:218); wimp3 (:216) — импульс в узле 3 сетки из семи узлов. ') + CL + '.';
const N_TRAV = L('wave_travelling_n : forall N (F : grid_fn) n, (0 < N)%nat -> gperiodic N F -> forall j, fst (wave_iter 1 N F (fun k => F (S k)) n) j == F (n + j)%nat /¤ snd (wave_iter 1 N F (fun k => F (S k)) n) j == F (S (n + j)) (ProcessWaveProcess.v:266); один шаг — wave_travelling_step (:255). ') + CL + '.';
const N_DEP = 'wave_step_dep : forall s N (p1 c1 p2 c2 : grid_fn) j, c1 (ppred N j) == c2 (ppred N j) -> c1 j == c2 j -> c1 (S j) == c2 (S j) -> p1 j == p2 j -> wave_step s N p1 c1 j == wave_step s N p2 c2 j (ProcessWaveProcess.v:109). ' + CL + '.';
const N_IMP = L('wave_impulse_profile : wave_step (1#2) 5 wzero wimp 0 == 0 /¤ wave_step (1#2) 5 wzero wimp 1 == 1#2 /¤ wave_step (1#2) 5 wzero wimp 2 == 1 /¤ wave_step (1#2) 5 wzero wimp 3 == 1#2 /¤ wave_step (1#2) 5 wzero wimp 4 == 0 (ProcessWaveProcess.v:70). ') + CL + '.';
const N_VEL = 'wave_example_velocity_nonzero : wimp 2%nat - wzero 2%nat == 1 (ProcessWaveProcess.v:85). ' + CL + '.';
const N_ZV = L('wave_zero_velocity_profile : wave_step (1#2) 5 wimp wimp 0 == 0 /¤ wave_step (1#2) 5 wimp wimp 1 == 1#2 /¤ wave_step (1#2) 5 wimp wimp 2 == 0 /¤ wave_step (1#2) 5 wimp wimp 3 == 1#2 /¤ wave_step (1#2) 5 wimp wimp 4 == 0 (ProcessWaveProcess.v:90). ') + CL + '.';
const N_E = 'Definition wave_energy (s : Q) (N : nat) (a b : grid_fn) : Q := sum_Q_ns (fun j => (b j - a j) * (b j - a j)) N + s * sum_Q_ns (fun j => fd b j * fd a j) N (ProcessWaveConservation.v:83); a — прошлый уровень, b — текущий; fd — прямая разность соседних узлов.';
const N_ES = 'wave_energy_step : forall s N (a b : grid_fn), (0 < N)%nat -> a N == a 0%nat -> b N == b 0%nat -> b (S N) == b 1%nat -> wave_energy s N b (wave_step s N a b) == wave_energy s N a b (ProcessWaveConservation.v:120). ' + CL + '.';
const N_EC = 'wave_energy_conserved : forall s N (u0 u1 : grid_fn) n, (0 < N)%nat -> gperiodic N u0 -> gperiodic N u1 -> wave_energy s N (fst (wave_iter s N u0 u1 n)) (snd (wave_iter s N u0 u1 n)) == wave_energy s N u0 u1 (ProcessWaveConservation.v:146) — при всяком s; периодичность профиля шаг сохраняет (wave_iter_gperiodic, ProcessWaveProcess.v:236). ' + CL + '.';
const N_GREEN = 'wave_green : forall N (b w : grid_fn), (0 < N)%nat -> b N == b 0%nat -> b (S N) == b 1%nat -> w N == w 0%nat -> sum_Q_ns (fun j => fd b j * fd w j) N == - sum_Q_ns (fun j => w j * wlap N b j) N (ProcessWaveConservation.v:96) — суммирование по частям через abel_periodic (FiniteDifference.v:183). ' + CL + '.';
const N_NAIVE = L('wave_energy_naive_not_conserved : wave_energy_naive (1#2) 5 wzero wimpP == 2 /¤ wave_energy_naive (1#2) 5 wimpP (wave_step (1#2) 5 wzero wimpP) == 1 (ProcessWaveConservation.v:179); wave_energy_naive (:165) — с потенциальной частью s * sum (fd b)^2 на одном уровне; wimpP (:169) — периодический импульс. ') + CL + '.';
const N_CROSS = L('wave_energy_cross_example : wave_energy (1#2) 5 wzero wimpP == 1 /¤ wave_energy (1#2) 5 wimpP (wave_step (1#2) 5 wzero wimpP) == 1 (ProcessWaveConservation.v:184). ') + CL + '.';
const N_LOW = 'wave_energy_lower : forall s N (a b : grid_fn), 0 <= s -> a N == a 0%nat -> b N == b 0%nat -> (1 - s) * sum_Q_ns (fun j => (b j - a j) * (b j - a j)) N <= wave_energy s N a b (ProcessWaveConservation.v:211). ' + CL + '.';
const N_NN = 'wave_energy_nonneg : forall s N (a b : grid_fn), 0 <= s -> s <= 1 -> a N == a 0%nat -> b N == b 0%nat -> 0 <= wave_energy s N a b (ProcessWaveConservation.v:245). ' + CL + '.';
const N_INC = 'wave_cfl_increment_bound : forall s N (u0 u1 : grid_fn) n, (0 < N)%nat -> 0 <= s -> gperiodic N u0 -> gperiodic N u1 -> (1 - s) * (сумма квадратов разности двух уровней после n шагов) <= wave_energy s N u0 u1 (ProcessWaveConservation.v:260) — при всяком n; оценка содержательна при s < 1. ' + CL + '.';
const N_IFF = 'wave_energy_nonneg_iff_cfl : forall s N, (0 < N)%nat -> Nat.even N = true -> 0 <= s -> ((forall a b : grid_fn, gperiodic N a -> gperiodic N b -> 0 <= wave_energy s N a b) <-> s <= 1) (ProcessWaveConservation.v:360); свидетель — wave_alt_energy (:341): энергия знакопеременного состояния равна N * (4 * (1 - s)). ' + CL + '.';
const N_UNST = 'wave_unstable_beyond_cfl : forall s N, (0 < N)%nat -> Nat.even N = true -> 1 < s -> forall B : Q, exists n, B < Qabs (snd (wave_iter s N wnalt walt n) 0%nat) (ProcessWaveConservation.v:485); walt (:305) — профиль 1, −1, 1, −1, …; wnalt (:306) — противоположный. ' + CL + '.';
const N_GROW = L('wave_growth_example : snd (wave_iter 2 2 wnalt walt 1) 0 == - (5) /¤ snd (wave_iter 2 2 wnalt walt 2) 0 == 29 /¤ snd (wave_iter 2 2 wnalt walt 3) 0 == - (169) (ProcessWaveConservation.v:505); начальное значение текущего уровня в узле 0 равно 1. ') + CL + '.';
const N_MODE = L('wave_alt_mode_iter : forall s N y0 y1 n, (0 < N)%nat -> Nat.even N = true -> forall j, fst (wave_iter s N (fun k => y0 * walt k) (fun k => y1 * walt k) n) j == fst (wosc (2 - 4 * s) y0 y1 n) * walt j /¤ snd (wave_iter s N (fun k => y0 * walt k) (fun k => y1 * walt k) n) j == snd (wosc (2 - 4 * s) y0 y1 n) * walt j (ProcessWaveConservation.v:407); wosc (:393) — рекуррента y_{n+1} = q y_n − y_{n−1}; один шаг — wave_alt_mode_step (:383). ') + CL + '.';
const N_SD = 'wosc_second_difference : forall q y0 y1 n, snd (wosc q y0 y1 (S n)) - 2 * snd (wosc q y0 y1 n) + fst (wosc q y0 y1 n) == (q - 2) * snd (wosc q y0 y1 n) (ProcessWaveConservation.v:401); при q = 2 − 4 s правая часть равна −4 s y. Общих определений с осциллятором Главы 8.5 (явный метод Эйлера для пары) нет. ' + CL + '.';
const N_DRIFT = L('wave_const_mode_drift : forall s N n j, fst (wave_iter s N (fun _ => 0) (fun _ => 1) n) j == inject_Z (Z.of_nat n) /¤ snd (wave_iter s N (fun _ => 0) (fun _ => 1) n) j == inject_Z (Z.of_nat n) + 1 (ProcessWaveConservation.v:524); энергия этого состояния равна N на каждом шаге (wave_const_mode_energy, :540). ') + CL + '.';
const ALL19 = 'все 19 объявлений ProcessWaveProcess.v: Closed under the global context';
const ALL41 = 'все 41 объявление ProcessWaveConservation.v: Closed under the global context';

// ================================================================ глава IX.3
{
  const { fix, add, save, claimOf } = open('part09-ch03');
  const C33 = 'Доказано и *сохранение дискретной энергии*: для схемы чехарды она имеет неочевидную (зависящую от двух уровней) форму и на периодической сетке сохраняется на всём процессе, при любом $s$ (см. § «Энергия и граница»).';
  const C35 = L('Чего глава *не* делает: она не строит завершённую непрерывную волну, интеграл её энергии, дисперсионный анализ и поведение при $t¤to¤infty$ — это роль-пределы.');
  const C40 = '*Первый* — конечная схема над ℚ: чехарда, локальная причинность, конечная скорость, конкретное распространение, сохранение дискретной энергии — доказаны без аксиом.';
  const C56 = L('Условие устойчивости (CFL) $s¤le1$ нужно для энергетического слоя — при нём дискретная энергия неотрицательна, — а не для самой причинности.');
  const C103 = 'Отсюда немедленно — локальная причинность: если волна «молчит» в узле и его соседях (и молчала там на прошлом шаге), она будет молчать в этом узле и на следующем шаге:';
  const C128 = L('Поместим острый импульс в узел $2$ пятиузловой сетки (прошлый уровень нулевой: возмущение только что возникло) и сделаем шаг с $s=¤tfrac12$.');
  const CFORM = L('E^n ¤;=¤; ¤sum_j ¤bigl(u^{n+1}_j-u^n_j¤bigr)^2 ¤;+¤; s¤sum_j ¤bigl(u^{n+1}_{j+1}-u^{n+1}_j¤bigr)¤bigl(u^{n}_{j+1}-u^{n}_j¤bigr).');
  const CCONS = 'На периодической сетке эта величина сохраняется на каждом шаге и на всём процессе, при любом $s$: это тождество конечных сумм (суммирование по частям).';
  const CNAIVE = 'Выбор энергии существен: величина с потенциальной частью на одном уровне той же схемой не сохраняется.';
  const CCFL = L('Условие Куранта $s¤le1$ получает здесь точный смысл: при нём энергия неотрицательна и ограничивает приращения по времени на всех шагах; на сетке с чётным числом узлов неотрицательность энергии равносильна $s¤le1$, а при $s>1$ значения решения превосходят любую границу.');
  const CBOUND = 'Граница главы — завершённая непрерывная волна $u(x,t)$, интеграл её энергии, непрерывный предел и дисперсионный анализ (как меняется скорость с длиной волны).';
  const CFIN = 'Доказано конечное: причинность, конечная скорость распространения и сохранение дискретной энергии над ℚ.';
  const CIT = 'для схемы чехарды им служит специальная дискретная энергия, связывающая два уровня, и её сохранение доказано без перехода к пределу.';
  const C178 = L('Рядом — энергетический слой: сохранение дискретной энергии на периодической сетке и условие устойчивости $s¤le1$ (CFL), при котором она неотрицательна. Доказанное ядро — причинность, конечная скорость и сохранение дискретной энергии.');
  const C186 = 'Дискретная энергия — роль-сохраняющаяся величина. А завершённая волна и интеграл её энергии — роль-пределы.';
  const CT1 = L('конечная скорость; сохранение дискретной энергии; CFL $s¤le1$');
  const CT2 = 'фронт; дискретная энергия; интеграл энергии как предел';
  const C216 = 'Дискретная энергия — конечная сумма на каждом шаге — построена и сохраняется.';
  const F1 = 'Законы на всём процессе — `ProcessWaveProcess.v` (состояние после $n$ шагов, конечная скорость и конус зависимости за $n$ шагов; 17 утверждений, 0 аксиом) и `ProcessWaveConservation.v` (сохранение дискретной энергии на всём процессе, точность условия Куранта; 34 утверждения, 0 аксиом).';
  const F2 = L('На одной пространственной моде — знакопеременном профиле на сетке с чётным числом узлов — схема есть разностное уравнение осциллятора $y_{n+1}-2y_n+y_{n-1}=-4s¤,y_n$ (`wave_alt_mode_iter`, `wosc_second_difference`, `ProcessWaveConservation.v`).');
  const F3 = 'Общая форма — `wave_step_dep` (`ProcessWaveProcess.v`): два состояния, совпадающие в узлах $j-1$, $j$, $j+1$ текущего уровня и в узле $j$ прошлого, дают в узле $j$ одно значение.';
  const F4 = 'За $n$ шагов — `wave_finite_speed_n` (`ProcessWaveProcess.v`).';
  const F5A = 'Все пять узлов — `wave_impulse_profile` (`ProcessWaveProcess.v`).';
  const F5B = 'В этих данных прошлый уровень нулевой, а текущий — импульс: сеточная скорость в узле $2$ ненулевая (`wave_example_velocity_nonzero`).';
  const F5C = L('При нулевой скорости (прошлый уровень равен текущему) тот же импульс за шаг расходится на две половины: узлы $1$ и $3$ получают по $¤tfrac12$, узел $2$ обнуляется (`wave_zero_velocity_profile`).');
  const F6 = L('В обозначениях главы условие Куранта — $s¤le1$.');
  const F7A = '`wave_finite_speed_n` в `ProcessWaveProcess.v`: если оба начальных уровня равны нулю на $[a,b]$, то после $n$ шагов оба уровня равны нулю на $[a+n,b-n]$ — при всяком $s$; состояние после $n$ шагов — `wave_iter`.';
  const F7B = 'То же для совпадающих начальных данных — `wave_dependence_cone_n`: значение в узле $j$ после $n$ шагов определяется начальными данными на $[j-n,j+n]$ (`wave_value_depends_on_cone`).';
  const F7C = 'Граница достигается: за два шага возмущение доходит до узла на расстоянии $2$ и не доходит до узла на расстоянии $3$ (`wave_two_steps_reach`).';
  const F7D = 'При $s=1$ бегущий периодический профиль переносится точно, на узел за шаг (`wave_travelling_n`). 0 аксиом.';
  const F8A = '`wave_energy` и `wave_energy_conserved` в `ProcessWaveConservation.v`: для периодических начальных уровней энергия после $n$ шагов равна начальной — при всяком $s$, всяком $N>0$ и всяком $n$; один шаг — `wave_energy_step`.';
  const F8B = L('Величина с потенциальной частью на одном уровне не сохраняется: на периодическом импульсе ($N=5$, $s=¤tfrac12$) она равна $2$ до шага и $1$ после (`wave_energy_naive_not_conserved`), а перекрёстная — $1$ и $1$ (`wave_energy_cross_example`). 0 аксиом.');
  const F9A = L('При $s¤ge0$ энергия не меньше $(1-s)¤sum_j(u^{n+1}_j-u^n_j)^2$ (`wave_energy_lower`); отсюда неотрицательность при $0¤le s¤le1$ (`wave_energy_nonneg`) и оценка приращений на всех шагах (`wave_cfl_increment_bound`).');
  const F9B = 'Точность условия — `wave_energy_nonneg_iff_cfl`; рост при $s>1$ — `wave_unstable_beyond_cfl` (знакопеременный профиль; при $s=2$ на сетке из двух узлов значения в узле $0$: $1,-5,29,-169$ — `wave_growth_example`).';
  const F9C = 'Энергия ограничивает приращения, а не сами значения: постоянный профиль с единичной скоростью уходит линейно при любом $s$ (`wave_const_mode_drift`). Все — `ProcessWaveConservation.v`, 0 аксиом.';

  // «Что эта глава утверждает» (вопрос 1, вариант 1)
  fix('Чего глава *не* делает: она не доказывает', null, { claim: C33, theorem: 'wave_energy_conserved', file: WC, assumptions: CL,
    note: DONE + ' (вопрос 1 шага 3, вариант 1): сохранение дискретной энергии доведено делом и названо на странице. ' + N_EC });
  add({ theorem: null, file: WC, claim: C35,
    note: DONE + ' (вопрос 1 шага 3, вариант 1). Верно: завершённой непрерывной волны, интеграла её энергии, дисперсионного анализа и поведения при t → ∞ в формализации нет; энергия в ProcessWaveConservation.v — конечная сумма на каждом шаге.' });
  fix('*Первый* — конечная схема над ℚ: чехарда, локальная причинность, конечная скорость, конкретное распространение — доказаны', null, { claim: C40,
    note: DONE + ' (вопрос 1 шага 3, вариант 1): добавлено «сохранение дискретной энергии». Print Assumptions всех объявлений ProcessWaveEnergy.v (9), ProcessWaveProcess.v (19) и ProcessWaveConservation.v (41) — Closed under the global context; строк Axiom, Parameter, Admitted в трёх файлах нет.' });
  add({ theorem: 'wave_energy_conserved', file: WC, assumptions: CL, claim: C40, note: '«Сохранение дискретной энергии — доказано без аксиом»: ' + N_EC });
  fix(L('Условие устойчивости (CFL) $c^2¤le1$ нужно'), null, { claim: C56, theorem: 'wave_energy_nonneg', file: WC, assumptions: CL,
    note: DONE + ' (вопрос 1 шага 3, вариант 1): условие записано в обозначениях главы (s <= 1) и названо, что оно даёт. ' + N_NN + ' Леммы причинности стоят под квантором «для всякого s» без условий.' });

  // причинность и конечная скорость
  fix('Отсюда немедленно — локальная причинность: если волна «молчит» в узле и его соседях (и молчала там на прошлом шаге), она будет молчать в этом узле и дальше', 'wave_step_local_zero', { claim: C103,
    note: DONE + ': «и дальше» заменено на «и на следующем шаге» — лемма говорит об одном следующем шаге. Lemma wave_step_local_zero (ProcessWaveEnergy.v:62): нули в j-1, j, j+1 текущего уровня и в j прошлого дают нуль следующего уровня в j. На n шагов — wave_quiet_n (ProcessWaveProcess.v:172): при тихой окрестности радиуса n.' });
  fix('За $n$ шагов фронт продвигается', null, { theorem: 'wave_finite_speed_n', file: WP, assumptions: CL,
    note: KEPT + 'утверждение о n шагах теперь доказано: ' + N_FS + ' Состояние после n шагов: ' + N_ITER });
  add({ theorem: 'wave_dependence_cone_n', file: WP, assumptions: CL, claim: claimOf('За $n$ шагов фронт продвигается'),
    note: '«Дискретный аналог конуса влияния»: ' + N_CONE });

  // пример (место 3.2; вопрос 2, вариант 1)
  fix('Поместим острый импульс в узел $2$ пятиузловой сетки (нулевая', null, { claim: C128, theorem: 'wave_impulse_profile', file: WP, assumptions: CL,
    note: DONE + ' (вопрос 2 шага 3, вариант 1): данные примера названы так, как они взяты в леммах, — прошлый уровень wzero, текущий wimp. ' + N_IMP });
  add({ theorem: 'wave_impulse_profile', file: WP, assumptions: CL, claim: claimOf('Пик в узле $2$ становится равным'),
    note: KEPT + 'все пять узлов теперь записаны одной леммой: ' + N_IMP });

  // раздел «Энергия и граница» (вопрос 1, вариант 1)
  fix('существует дискретный сохраняющийся аналог', null, { theorem: 'wave_energy', file: WC,
    note: KEPT + 'величина теперь определена: ' + N_E });
  add({ theorem: 'wave_energy', file: WC, claim: CFORM, note: DONE + ' (вопрос 1 шага 3, вариант 1): новая формула. ' + N_E + ' На странице a = u^n, b = u^{n+1}.' });
  fix('Честно: в настоящем изложении он', null, { claim: CCONS, theorem: 'wave_energy_conserved', file: WC, assumptions: CL,
    note: DONE + ' (вопрос 1 шага 3, вариант 1): на месте слов «не доказан». ' + N_EC });
  add({ theorem: 'wave_energy_step', file: WC, assumptions: CL, claim: CCONS, note: '«На каждом шаге»: ' + N_ES });
  add({ theorem: 'wave_green', file: WC, assumptions: CL, claim: CCONS, note: '«Суммирование по частям»: ' + N_GREEN });
  add({ theorem: 'wave_energy_naive_not_conserved', file: WC, assumptions: CL, claim: CNAIVE, note: DONE + ': новая фраза. ' + N_NAIVE });
  add({ theorem: 'wave_energy_nonneg', file: WC, assumptions: CL, claim: CCFL, note: DONE + ': новый абзац. ' + N_NN });
  add({ theorem: 'wave_cfl_increment_bound', file: WC, assumptions: CL, claim: CCFL, note: N_INC });
  add({ theorem: 'wave_energy_nonneg_iff_cfl', file: WC, assumptions: CL, claim: CCFL, note: N_IFF });
  add({ theorem: 'wave_unstable_beyond_cfl', file: WC, assumptions: CL, claim: CCFL, note: N_UNST });
  add({ theorem: null, file: WC, claim: CBOUND,
    note: DONE + ' (вопрос 1 шага 3, вариант 1). Верно: непрерывной волны, интеграла её энергии, предела измельчения и дисперсионного анализа в формализации нет.' });
  fix('Доказано конечное и робастное', null, { claim: CFIN,
    note: DONE + ' (вопрос 1 шага 3, вариант 1): к причинности и конечной скорости добавлено сохранение дискретной энергии. Все утверждения — над Q, без аксиом.' });
  add({ theorem: 'wave_finite_speed_n', file: WP, assumptions: CL, claim: CFIN, note: N_FS });
  add({ theorem: 'wave_energy_conserved', file: WC, assumptions: CL, claim: CFIN, note: N_EC });
  fix('(его можно доказать и без перехода к пределу', null, { claim: CIT, theorem: 'wave_energy_conserved', file: WC, assumptions: CL,
    note: DONE + ' (вопрос 1 шага 3, вариант 1: текст курсива принят автором). «Сохранение доказано без перехода к пределу»: ' + N_EC });

  // разбор (вопрос 1, вариант 1)
  fix(L('Условие устойчивости $c^2¤le1$ (CFL) и сохранение энергии'), null, { claim: C178, theorem: 'wave_energy_conserved', file: WC, assumptions: CL,
    note: DONE + ' (вопрос 1 шага 3, вариант 1): энергетический слой назван доказанным. ' + N_EC });
  add({ theorem: 'wave_energy_nonneg', file: WC, assumptions: CL, claim: C178, note: L('«Условие устойчивости $s¤le1$, при котором она неотрицательна»: ') + N_NN });
  add({ theorem: 'wave_energy_conserved', file: WC, assumptions: CL, claim: C186, note: DONE + ': новая фраза. ' + N_EC });
  add({ theorem: 'wave_energy_conserved', file: WC, assumptions: CL, claim: CT1, note: DONE + ': строка таблицы. ' + N_EC });
  add({ theorem: 'wave_energy', file: WC, claim: CT2, note: DONE + ': строка таблицы. ' + N_E });
  add({ theorem: 'wave_energy_conserved', file: WC, assumptions: CL, claim: C216, note: DONE + ': новая фраза. ' + N_EC });
  add({ theorem: 'wave_energy', file: WC, claim: C216, note: '«Конечная сумма на каждом шаге»: ' + N_E });

  // сноска 1
  add({ theorem: null, file: WP, claim: F1, page_price: '0 аксиом', assumptions: ALL19,
    note: DONE + ': новые опорные файлы в сноске. src/process/ProcessWaveProcess.v: 17 Qed и два определения; строк Axiom, Parameter, Admitted нет.' });
  add({ theorem: null, file: WC, claim: F1, page_price: '0 аксиом', assumptions: ALL41,
    note: 'src/process/ProcessWaveConservation.v: 34 Qed и семь определений; строк Axiom, Parameter, Admitted нет.' });

  // сноски 2–6
  add({ theorem: 'wave_alt_mode_iter', file: WC, assumptions: CL, claim: F2, note: DONE + ': новая фраза. ' + N_MODE });
  add({ theorem: 'wosc_second_difference', file: WC, assumptions: CL, claim: F2, note: N_SD });
  add({ theorem: 'wave_step_dep', file: WP, assumptions: CL, claim: F3, note: DONE + ': новая фраза. ' + N_DEP });
  add({ theorem: 'wave_finite_speed_n', file: WP, assumptions: CL, claim: F4, note: DONE + ': новая фраза. ' + N_FS });
  add({ theorem: 'wave_impulse_profile', file: WP, assumptions: CL, claim: F5A, note: DONE + ': новая фраза. ' + N_IMP });
  add({ theorem: 'wave_example_velocity_nonzero', file: WP, assumptions: CL, claim: F5B, note: N_VEL });
  add({ theorem: 'wave_zero_velocity_profile', file: WP, assumptions: CL, claim: F5C, note: N_ZV });
  add({ theorem: 'wave_energy_nonneg_iff_cfl', file: WC, assumptions: CL, claim: F6,
    note: DONE + ': новая фраза. Шапка ProcessWaveEnergy.v пишет «CFL c² ≤ 1» при s = c²(Δt/Δx)²; условием на схему служит s <= 1: ' + N_IFF });

  // сноска 7
  add({ theorem: 'wave_finite_speed_n', file: WP, assumptions: CL, claim: F7A, note: DONE + ': новая сноска. ' + N_FS });
  add({ theorem: 'wave_iter', file: WP, claim: F7A, note: N_ITER });
  add({ theorem: 'wave_dependence_cone_n', file: WP, assumptions: CL, claim: F7B, note: N_CONE });
  add({ theorem: 'wave_value_depends_on_cone', file: WP, assumptions: CL, claim: F7B, note: N_VCONE });
  add({ theorem: 'wave_two_steps_reach', file: WP, assumptions: CL, claim: F7C, note: N_TWO });
  add({ theorem: 'wave_travelling_n', file: WP, assumptions: CL, claim: F7D, page_price: '0 аксиом', note: N_TRAV });

  // сноска 8
  add({ theorem: 'wave_energy', file: WC, claim: F8A, note: DONE + ': новая сноска. ' + N_E });
  add({ theorem: 'wave_energy_conserved', file: WC, assumptions: CL, claim: F8A, note: N_EC });
  add({ theorem: 'wave_energy_step', file: WC, assumptions: CL, claim: F8A, note: N_ES });
  add({ theorem: 'wave_energy_naive_not_conserved', file: WC, assumptions: CL, claim: F8B, page_price: '0 аксиом', note: N_NAIVE });
  add({ theorem: 'wave_energy_cross_example', file: WC, assumptions: CL, claim: F8B, page_price: '0 аксиом', note: N_CROSS });

  // сноска 9
  add({ theorem: 'wave_energy_lower', file: WC, assumptions: CL, claim: F9A, note: DONE + ': новая сноска. ' + N_LOW });
  add({ theorem: 'wave_energy_nonneg', file: WC, assumptions: CL, claim: F9A, note: N_NN });
  add({ theorem: 'wave_cfl_increment_bound', file: WC, assumptions: CL, claim: F9A, note: N_INC });
  add({ theorem: 'wave_energy_nonneg_iff_cfl', file: WC, assumptions: CL, claim: F9B, note: N_IFF });
  add({ theorem: 'wave_unstable_beyond_cfl', file: WC, assumptions: CL, claim: F9B, note: N_UNST });
  add({ theorem: 'wave_growth_example', file: WC, assumptions: CL, claim: F9B, note: N_GROW });
  add({ theorem: 'wave_const_mode_drift', file: WC, assumptions: CL, claim: F9C, page_price: '0 аксиом', note: N_DRIFT });

  save();
}

// ================================================================ глава IX.1
{
  const { add, save, claimOf } = open('part09-ch01');
  // волна в триптихе: конечная скорость на всём процессе
  add({ theorem: 'wave_finite_speed_n', file: WP, assumptions: CL, claim: claimOf('Уравнение второго порядка по времени; процесс *распространяет*'),
    note: KEPT + '«фронт продвигается не более чем на один узел за шаг» теперь доказано на всём процессе: ' + N_FS });
  save();
}
