// Часть IX, шаг 4, страницы (2026-11-23, слово автора «Делай»): 7 правок главы IX.5 внесены по варианту 1
// развилки 1 (формула антисимметрии на странице — B(k,l,m) = −B(m,l,k), по проверяемой и переносимой модам).
// Формализация — новый src/navier_stokes/GalerkinAdvection.v; прежние файлы не менялись.
// Запуск: node patch-p09-step-04-pages.cjs  (затем relocate + merge по part09-ch05). Повторяем.
// Внимание: L() превращает знак «¤» в обратную косую черту.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 23.11 (Часть IX, шаг 4, слово автора)';
const KEPT = DONE + ' (формализацией; текст фразы не менялся): ';
const CL = 'Closed under the global context';
const GA = 'src/navier_stokes/GalerkinAdvection.v';
const GS = 'src/navier_stokes/GalerkinSystem.v';
const AE = 'src/navier_stokes/AdvectionEnergyConservation.v';
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
const N_NL = 'Definition nl (B : nat -> nat -> nat -> Q) (K : nat) (a : nat -> Q) (k : nat) : Q := sum_Q_ns (fun l => sum_Q_ns (fun m => B k l m * a l * a m) K) K (GalerkinAdvection.v:78) — нелинейный член моды k: k — проверяемая мода, l — переносящая, m — переносимая.';
const N_ADV = 'Definition adv (T : nat -> nat -> nat -> Q) (k l m : nat) : Q := T k l m - T m l k (GalerkinAdvection.v:141) — антисимметризация по первому и третьему индексу.';
const N_AA = 'adv_antisym : forall T k l m, adv T k l m == - adv T m l k (GalerkinAdvection.v:143) — для всякой сырой связи T; посылок нет. ' + CL + '.';
const N_AEZ = 'adv_energy_zero : forall T K (a : nat -> Q), sum_Q_ns (fun k => a k * nl (adv T) K a k) K == 0 (GalerkinAdvection.v:186) — для всякой сырой связи и всякого состояния; оценка связи не используется. Для сырой связи записи NSCoupling — raw_coupling_adv_energy_zero (:211). ' + CL + '.';
const N_PAIR = L('adv_pair_nl : forall a : nat -> Q, nl (adv T_pair) 2 a 0 == a 0 * a 1 /¤ nl (adv T_pair) 2 a 1 == - (a 0 * a 0) (GalerkinAdvection.v:225); T_pair (:217) — сырая связь пары мод: T 0 0 1 = 1, прочие значения нулевые. На состоянии (1, 1) — adv_nl_nonzero (:234): нелинейные члены 1 и −1. ') + CL + '.';
const N_NMZ = 'nl_mode_zero : forall (nsc : NSCoupling) K k (a : modal_state), inner_double_sum K k a == 0 (GalerkinAdvection.v:127) — при всякой записи посылок; inner_double_sum есть nl B_coeff (nl_Bcoeff_is_inner, :123). Общая причина — antisym_quadratic_form_zero (:96): квадратичная форма с коэффициентом, антисимметричным по своим двум индексам, равна нулю; lm_antisym_nl_zero (:113). ' + CL + '.';
const N_GFV = 'grhs_formal_is_viscous : forall (nsc : NSCoupling) nu K (a : modal_state) k, grhs nu B_coeff K a k == - nu * wgt k * a k (GalerkinAdvection.v:272). ' + CL + '.';
const N_GRHS = 'Definition grhs (nu : Q) (B : nat -> nat -> nat -> Q) (K : nat) (a : nat -> Q) (k : nat) : Q := - nu * wgt k * a k + nl B K a k (GalerkinAdvection.v:251); wgt k = (k+1)^2 (:243) — вес моды в энстрофии GalerkinSystem.v.';
const N_GSTEP = 'Definition gstep (nu : Q) (B : nat -> nat -> nat -> Q) (K : nat) (dt : Q) (a : nat -> Q) : nat -> Q := fun k => a k + dt * grhs nu B K a k (GalerkinAdvection.v:255) — шаг явной схемы; без связи он вязкий (gstep_zero_coupling, :281).';
const N_GTRAJ = 'Fixpoint gtraj (nu : Q) (B : nat -> nat -> nat -> Q) (K : nat) (dt : Q) (a : modal_state) (n : nat) : modal_state (GalerkinAdvection.v:259) — состояние после n шагов gstep.';
const N_GER = 'galerkin_energy_rate : forall nu T K (a : nat -> Q), sum_Q_ns (fun k => a k * grhs nu (adv T) K a k) K == - (2) * nu * modal_enstrophy K a (GalerkinAdvection.v:294) — скорость энергии вдоль правой части выведена, а не положена определением; при nu >= 0 она неположительна (galerkin_energy_rate_nonpos, :308), при nu = 0 нулевая (galerkin_inviscid_energy_rate, :319). ' + CL + '.';
const N_GSE = 'galerkin_step_energy : forall nu T K dt (a : nat -> Q), modal_energy K (gstep nu (adv T) K dt a) == modal_energy K a - 2 * nu * dt * modal_enstrophy K a + (1#2) * dt * dt * sum_Q_ns (fun k => grhs nu (adv T) K a k * grhs nu (adv T) K a k) K (GalerkinAdvection.v:352); общее тождество шага — energy_step_identity (:327); вычисленный шаг — galerkin_transfer_example (:367). ' + CL + '.';
const N_ERF = 'Theorem energy_rate_formula : forall nu K (a : modal_state), total_energy_rate nu K a == -(2) * nu * modal_enstrophy K a (GalerkinSystem.v:393); total_energy_rate (:364) = viscous_energy_rate (:149, по определению −2·nu·Omega) + nonlinear_energy_rate (:350, кубическая сумма). После развёртывания это nonlinear_energy_zero. ' + CL + '.';
const N_NEZ = 'Theorem nonlinear_energy_zero : forall K (a : modal_state), triple_sum K a == 0 (GalerkinSystem.v:326) — нуль суммы нулей: при антисимметрии по (l, m) нелинейный член каждой моды равен нулю (nl_mode_zero, GalerkinAdvection.v:127). ' + CL + '.';
const N_BA = 'Lemma B_antisym : forall k l m, B_coeff k l m == -(B_coeff k m l) (GalerkinSystem.v:249); Definition B_coeff (k l m : nat) : Q := B_raw k l m - B_raw k m l (:245), B_raw — поле записи посылок NSCoupling. ' + CL + '.';
const N_BURG = 'Theorem burgers_conserves_energy : forall (u : grid_fn) N, is_periodic N u -> sum_Q_ns (energy_flux_burgers u) N == 0 (AdvectionEnergyConservation.v:118) — телескопирование кубов на периодической сетке. ' + CL + '.';
const ALL31 = 'все 31 объявление GalerkinAdvection.v: Closed under the global context';

// ================================================================ глава IX.5
{
  const { fix, add, save, claimOf } = open('part09-ch05');
  const C58 = 'Ключевое свойство нелинейности — антисимметрия коэффициента по проверяемой и переносимой модам, $B(k,l,m) = -B(m,l,k)$; в формализации это лемма: коэффициент задан как антисимметризация абстрактной связи.[^2]';
  const C78 = L('В модальном (галёркинском) слое это записано как тождество для скорости энергии вдоль правой части системы, $¤sum_k a_k F_k(a) = -2¤nu¤Omega$ (`galerkin_energy_rate`, над рациональными амплитудами), и как точное тождество шага схемы, $E(a^{n+1}) = E(a^n) - 2¤nu¤,¤Delta t¤,¤Omega + ¤tfrac12 ¤Delta t^2 ¤sum_k F_k^2$ (`galerkin_step_energy`); классическая запись $dE/dt$ — его непрерывное чтение.');
  const C126 = L('*Rules*: на всех уровнях — сетка, конечно-разностная схема $u^{n+1}=u^n+¤Delta t ¤mathcal L_h u^n$ (для волны — двухслойная, для Навье–Стокса — на амплитудах мод) и конечные законы (энергия, масса, причинность, максимум).');
  const F1 = 'Система амплитуд с переносящей нелинейностью, её шаг и траектория — `GalerkinAdvection.v` (23 утверждения, 0 аксиом; теоремы о новой системе записи посылок не берут).';
  const F2A = '`adv_antisym` в `GalerkinAdvection.v` — лемма: `adv T k l m := T k l m - T m l k`, `T` — произвольная сырая связь; аксиом и посылок нет.';
  const F2B = L('Теорема `adv_energy_zero` формализует, что конвекция *сохраняет* энергию (лишь перебрасывает её между модами), не создавая и не уничтожая — дискретный аналог того, что $¤int (u¤cdot¤nabla u)¤cdot u = 0$; перенос при этом ненулевой: на двух модах система имеет вид $da_0/dt=a_0a_1$, $da_1/dt=-a_0^2$ (`adv_pair_nl`).');
  const F2C = 'Прежний коэффициент `B_coeff` (`GalerkinSystem.v`) антисимметричен по двум последним индексам, $B(k,l,m)=-B(k,m,l)$ (`B_antisym`);';
  const F2D = 'при такой антисимметрии нелинейный член каждой моды равен нулю (`nl_mode_zero`), и правая часть системы совпадает с вязкой (`grhs_formal_is_viscous`).';
  const F2E = 'Сеточная форма сохранения — `burgers_conserves_energy` (`AdvectionEnergyConservation.v`).';
  const F3A = '`galerkin_energy_rate` и `galerkin_step_energy` (`GalerkinAdvection.v`): скорость энергии выведена из правой части системы, нелинейный вклад нулевой — `adv_energy_zero`.';
  const F3B = L('В `GalerkinSystem.v` то же тождество записано для состояния — `energy_rate_formula`: вязкий вклад $-2¤nu¤Omega$ взят там по определению, нелинейный вклад — `nonlinear_energy_zero`.');
  const F3C = 'Далее — `energy_bounded_by_initial`, `energy_monotone` (`EnergyEstimate.v`): $E$ монотонна и ограничена начальной, безусловно. Опираются на `B_antisym`.';
  const F3D = 'Далее — `energy_bounded_by_initial`, `energy_monotone` (`EnergyEstimate.v`): $E$ монотонна и ограничена начальной, безусловно.';
  const F7A = 'Правая часть системы, шаг явной схемы и состояние после $n$ шагов — `grhs`, `gstep`, `gtraj` в `GalerkinAdvection.v` (`navier_stokes/`); нелинейный член моды — `nl`.';
  const F7B = 'Правило отбора триад, давление и условие несжимаемости не формализованы.';

  // место 5.2: система амплитуд
  fix('ToS ведёт это как процесс — галёркинский (модальный)', 'triple_sum', { theorem: 'grhs', file: GA, assumptions: '',
    note: KEPT + 'система теперь объявлена: ' + N_GRHS + ' Шаг и траектория — gstep (:255), gtraj (:259). Правила отбора триад у коэффициента нет; давление и несжимаемость не формализованы (сноска 7).' });

  // место 5.1: антисимметрия (развилка 1, вариант 1)
  fix('Ключевое свойство нелинейности — антисимметрия коэффициента, $B(k,l,m) = -B(k,m,l)$', 'B_antisym', { claim: C58, theorem: 'adv_antisym', file: GA, assumptions: CL,
    note: DONE + ' (развилка 1, вариант 1): формула антисимметрии — по проверяемой и переносимой модам. ' + N_AA + ' ' + N_ADV });
  fix('Антисимметрия означает: нелинейность энергию только', 'nonlinear_energy_zero', { theorem: 'adv_energy_zero', file: GA, assumptions: CL,
    note: KEPT + '«перераспределяет» теперь доказано для связи, антисимметричной по (k, m): ' + N_AEZ });
  add({ theorem: 'adv_pair_nl', file: GA, assumptions: CL, claim: claimOf('Антисимметрия означает: нелинейность энергию только'),
    note: '«Перераспределяет» — перенос между модами ненулевой: ' + N_PAIR });

  // место 5.3: тождество скорости энергии
  fix('В модальном (галёркинском) слое это записано как эволюционное тождество', 'energy_rate_formula', { claim: C78, theorem: 'galerkin_energy_rate', file: GA, assumptions: CL,
    note: DONE + ': тождество записано вдоль правой части системы и для шага схемы. ' + N_GER });
  add({ theorem: 'galerkin_step_energy', file: GA, assumptions: CL, claim: C78, note: N_GSE });
  add({ theorem: 'galerkin_energy_rate', file: GA, assumptions: CL, claim: claimOf('Энергетическое тождество $dE/dt=-2'),
    note: KEPT + 'тождество теперь выведено из правой части системы: ' + N_GER });

  // синтез Части: схема шага
  fix('*Rules*: на всех уровнях — сетка, конечно-разностная схема', null, { claim: C126, theorem: 'gstep', file: GA, assumptions: '',
    note: DONE + ': оговорка о двухслойной схеме волны и о схеме на амплитудах мод. ' + N_GSTEP + ' Для волны шаг читает два уровня: wave_step (ProcessWaveEnergy.v:42), wave_iter (ProcessWaveProcess.v:128).' });

  // сноска 1
  add({ theorem: null, file: GA, claim: F1, page_price: '0 аксиом', assumptions: ALL31,
    note: DONE + ': новый файл в сноске. src/navier_stokes/GalerkinAdvection.v: 23 Qed и восемь определений; строк Axiom, Parameter, Admitted нет. Запись NSCoupling аргументом берут только четыре утверждения о прежнем коэффициенте и о сырой связи записи (nl_Bcoeff_is_inner, nl_mode_zero, grhs_formal_is_viscous, raw_coupling_adv_energy_zero).' });

  // сноска 2 (развилка 1, вариант 1)
  fix('`B_antisym` в `GalerkinSystem.v` — лемма: `B_coeff k l m := B_raw k l m - B_raw k m l`', 'B_antisym', { claim: F2A, theorem: 'adv_antisym', file: GA, assumptions: CL,
    note: DONE + ' (развилка 1, вариант 1): сноска переписана. ' + N_AA });
  add({ theorem: 'adv', file: GA, claim: F2A, note: N_ADV });
  add({ theorem: 'T', file: '', claim: F2A, assumptions: 'не применимо (связанная переменная)',
    note: '`T` на странице — связанная переменная определения adv и теорем о нём (forall T : nat -> nat -> nat -> Q): произвольная сырая связь, а не объявление формализации.' });
  fix('Она формализует, что конвекция *сохраняет* энергию', 'nonlinear_energy_zero', { claim: F2B, theorem: 'adv_energy_zero', file: GA, assumptions: CL,
    note: DONE + ' (развилка 1, вариант 1). ' + N_AEZ });
  add({ theorem: 'adv_pair_nl', file: GA, assumptions: CL, claim: F2B, note: N_PAIR });
  fix('`B_raw` — абстрактный параметр; аксиом в файле нет.', 'B_raw', { claim: F2C, theorem: 'B_antisym', file: GS, assumptions: CL,
    note: DONE + ' (развилка 1, вариант 1): прежний коэффициент назван с его антисимметрией. ' + N_BA });
  add({ theorem: 'B_coeff', file: GS, claim: F2C, note: 'Definition B_coeff (k l m : nat) : Q := B_raw k l m - B_raw k m l (GalerkinSystem.v:245); B_raw — поле записи посылок NSCoupling (:216).' });
  add({ theorem: 'nl_mode_zero', file: GA, assumptions: CL, claim: F2D, note: N_NMZ });
  add({ theorem: 'grhs_formal_is_viscous', file: GA, assumptions: CL, claim: F2D, note: N_GFV });
  add({ theorem: 'burgers_conserves_energy', file: AE, assumptions: CL, claim: F2E, note: N_BURG });

  // сноска 3: первая половина (место 5.3); вторая половина — место 5.4, шаг 5
  fix('`energy_rate_formula` (`GalerkinSystem.v`: $dE/dt=-2', 'energy_rate_formula', { claim: F3A, theorem: 'galerkin_energy_rate', file: GA, assumptions: CL,
    note: DONE + ': первая половина сноски. ' + N_GER });
  add({ theorem: 'galerkin_step_energy', file: GA, assumptions: CL, claim: F3A, note: N_GSE });
  add({ theorem: 'adv_energy_zero', file: GA, assumptions: CL, claim: F3A, note: N_AEZ });
  fix('нелинейный вклад нулевой — `nonlinear_energy_zero`)', 'nonlinear_energy_zero', { claim: F3B, assumptions: CL,
    note: DONE + ': названо, что стоит в прежнем файле. ' + N_NEZ });
  add({ theorem: 'energy_rate_formula', file: GS, assumptions: CL, claim: F3B, note: N_ERF });
  fix('и `energy_bounded_by_initial`, `energy_monotone` (`EnergyEstimate.v`): $E$ монотонна и ограничена начальной, безусловно. Опираются', 'energy_bounded_by_initial', { claim: F3C, verdict: 'mismatch-statement' });
  fix('и `energy_bounded_by_initial`, `energy_monotone` (`EnergyEstimate.v`): $E$ монотонна и ограничена начальной, безусловно.', 'energy_monotone', { claim: F3D, verdict: 'mismatch-statement' });

  // сноска 7 (место 5.2)
  add({ theorem: 'grhs', file: GA, claim: F7A, note: DONE + ': новая сноска. ' + N_GRHS });
  add({ theorem: 'gstep', file: GA, claim: F7A, note: N_GSTEP });
  add({ theorem: 'gtraj', file: GA, claim: F7A, note: N_GTRAJ });
  add({ theorem: 'nl', file: GA, claim: F7A, note: N_NL });
  add({ theorem: null, file: GA, claim: F7B,
    note: 'Верно: is_triad (TriadicInteraction.v:65) объявлено, но с коэффициентом не связано; давления и условия несжимаемости в каталоге navier_stokes нет.' });

  save();
}
