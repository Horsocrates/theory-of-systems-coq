// Часть IX, шаг 6, страницы (2026-11-23): 7 правок главы IX.5 — цена слоя («доменные аксиомы»), «стена»
// (сноска 6), итоговая таблица Части. Запускать ПОСЛЕ внесения правок по слову автора.
// Формализация — новый src/process/ProcessGrowthExponentGap.v; прежние файлы не менялись.
// Запуск: node patch-p09-step-06-pages.cjs  (затем relocate + merge по part09-ch05). Повторяем.
// Внимание: L() превращает знак «¤» в обратную косую черту.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 23.11 (Часть IX, шаг 6, слово автора)';
const KEPT = DONE + ' (формализацией; текст фразы не менялся): ';
const CL = 'Closed under the global context';
const GG = 'src/process/ProcessGrowthExponentGap.v';
const GS = 'src/navier_stokes/GalerkinSystem.v';
const AS = 'src/navier_stokes/AttackSynthesis.v';
const HA = 'src/navier_stokes/HonestAssessment.v';
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
const PRICE = 'По полной проверке допущений: в каталоге navier_stokes 39 файлов, 957 строк Qed; строк Axiom и Parameter нет; все теоремы и леммы, кроме одной, — Closed under the global context; galerkin_finite_regularity_capstone опирается на Classical_Prop.classic. Константа связи, её положительность и оценка связи — поля записи NSCoupling (GalerkinSystem.v:216), то есть посылки теорем.';
const N_LIN = 'linear_growth_uniform_in_step : forall C y0 T, 0 <= C -> 0 <= y0 -> 0 <= T -> exists U, forall N, lin_iter C (T / inject_Z (Z.of_nat (S N))) y0 (S N) <= U (ProcessGrowthExponentGap.v:88); lin_iter (:74) — рекуррента y_{n+1} = y_n + h C y_n; замкнутый вид — lin_iter_closed (:80); граница — из expt_bounded (ProcessExpLadder.v:519). ' + CL + '.';
const N_SUB = 'quadratic_growth_subcritical : forall C y0 T, 0 <= C -> 0 < y0 -> 0 <= T -> C * y0 * T < 1 -> forall N, quad_iter C (T / inject_Z (Z.of_nat (S N))) y0 (S N) <= y0 / (1 - C * y0 * T) (ProcessGrowthExponentGap.v:197); quad_iter (:117) — рекуррента y_{n+1} = y_n + h C y_n^2; ключ — quad_iter_upper_key (:161). ' + CL + '.';
const N_SUP = 'quadratic_growth_not_uniform_in_step : forall C y0 T M, 0 < C -> 0 < y0 -> 1 < C * y0 * T -> exists N, M < quad_iter C (T / inject_Z (Z.of_nat (S N))) y0 (S N) (ProcessGrowthExponentGap.v:265); ключ — quad_iter_lower_key (:219). ' + CL + '.';
const N_KR = 'k_rate_unbounded : forall C_lady E_0 nu M, 0 < C_lady -> 0 < E_0 -> 0 < nu -> exists K : nat, M < GronwallAnalysis.k_dependent_rate C_lady E_0 nu K (ProcessGrowthExponentGap.v:333); k_dependent_rate C E0 nu K = C*C*E0*K^2/nu (GronwallAnalysis.v:249). ' + CL + '.';
const N_MGP = 'Theorem millennium_gap_precise (AttackSynthesis.v:249) — конъюнкция пяти утверждений: оценка энергии под посылкой energy_decreasing; неотрицательность и монотонность по K числа k_dependent_rate; stretching_2d == 0 (то есть 0 == 0); неравенство Omega^2 <= E * P. Показателей 2 и 1 в утверждении нет. ' + CL + '.';
const ALL14 = 'все 14 объявлений ProcessGrowthExponentGap.v: Closed under the global context';

// ================================================================ глава IX.5
{
  const { fix, add, save } = open('part09-ch05');
  const C39 = 'не строит завершённое непрерывное решение и не выводит из уравнений движения ни коэффициентов связи, ни оценки нелинейного члена: они остаются посылками.';
  const C42 = '*Первый* — доказанное (без аксиом; условия стоят посылками теорем): диссипация энергии, регулярность для связей без вытяжения, для связей с вытяжением — условно.';
  const C148 = '| 9.3 Волна | причинность, конечная скорость, сохранение энергии | 0 аксиом |';
  const C150 = '| 9.5 Навье–Стокс | диссипация; регулярность без вытяжения; с вытяжением — условно | 0 аксиом; условия — посылки теорем; одна теорема на L3 |';
  const C153 = 'Навье–Стокс — доказательно богаче и аксиом тоже не несёт, но честно несёт посылки — оценку связи и оценку нелинейного члена в области — и упирается в открытую трёхмерную стену.';
  const F1D = '`millennium_gap_precise` (`AttackSynthesis.v`, свод доказанного по обе стороны зазора).';
  const F1Z = 'В каталоге 39 файлов и 957 доказанных утверждений (на 23.11.2026).';
  const F6A = L('Зазор между показателями $¤alpha=1$ и $¤alpha=2$ — `ProcessGrowthExponentGap.v` (`process/`): для линейной рекурренты $y_{n+1}=y_n+hCy_n$ значения в момент $T$ ограничены одним числом при всех шагах $h=T/N$ (`linear_growth_uniform_in_step`);');
  const F6B = 'для квадратичной $y_{n+1}=y_n+hCy_n^2$ такая граница есть при $Cy_0T<1$ (`quadratic_growth_subcritical`) и её нет при $Cy_0T>1$ (`quadratic_growth_not_uniform_in_step`).';
  const F6C = 'В терминах слоя: постоянная линейной оценки при фиксированном числе мод $K$ не ограничена по $K$ (`k_rate_unbounded`). 12 утверждений, 0 аксиом.';
  const F6D = '`millennium_gap_precise` (`AttackSynthesis.v`) — свод пяти фактов по обе стороны зазора; показателей в его утверждении нет.';
  const F6E = 'Что задача остаётся открытой, в `HonestAssessment.v` сказано комментарием: теоремы файла — числовые неравенства.';
  const F6F = 'Что энстрофия траектории подчиняется той или другой рекурренте, не доказано.';

  // место 5.9: цена
  fix('не строит завершённое непрерывное решение и не претендует на 0-аксиомность', null, { claim: C39, page_price: '',
    note: DONE + ': слова о цене заменены тем, что остаётся посылкой. Экземпляра записи NSCoupling с коэффициентами действительной адвекции нет (NSCoupling_inhabited, GalerkinSystem.v:228 — нулевая связь); оценка нелинейного члена в области — посылка region_invariant_iter (GalerkinEnstrophyRegion.v:517). ' + PRICE });
  fix('*Первый* — доказанное (с доменными аксиомами)', null, { claim: C42, page_price: 'без аксиом',
    note: DONE + ': «с доменными аксиомами» заменено на «без аксиом; условия стоят посылками теорем». ' + PRICE });
  fix('| 9.5 Навье–Стокс | диссипация, 2D регулярно, 3D условно', null, { claim: C150, page_price: '0 аксиом; одна теорема на L3',
    note: DONE + ': строка таблицы приведена к доказанному и к цене по компилятору. ' + PRICE });
  fix('Навье–Стокс — доказательно богаче, но честно несёт доменные аксиомы', null, { claim: C153, page_price: 'аксиом не несёт',
    note: DONE + ': «доменные аксиомы» заменены посылками. ' + PRICE });

  // итоговая таблица: волна
  fix('| 9.3 Волна | причинность, конечная скорость | 0 аксиом |', 'wave_step_interior_zero', { claim: C148,
    note: DONE + ': добавлено «сохранение энергии» (шаг 3). Причинность и конечная скорость — wave_step_local_zero, wave_step_interior_zero (ProcessWaveEnergy.v), на n шагов — wave_finite_speed_n (ProcessWaveProcess.v:154).' });
  add({ theorem: 'wave_energy_conserved', file: WC, assumptions: CL, claim: C148, page_price: '0 аксиом',
    note: '«Сохранение энергии»: wave_energy_conserved (ProcessWaveConservation.v:146) — дискретная энергия чехарды сохраняется на всём процессе на периодической сетке. ' + CL + '.' });

  // место 5.8: «стена»
  fix('Безусловная трёхмерная регулярность — открытая задача тысячелетия; в ToS она помечена точно', 'millennium_gap_precise', { theorem: 'quadratic_growth_not_uniform_in_step', file: GG, assumptions: CL,
    note: KEPT + '«между двумя показателями лежит зазор» теперь записано парой теорем о рекуррентах: ' + N_LIN + ' ' + N_SUP + ' Слова «ни один известный приём не закрывает» — слово автора; теоремой они быть не могут.' });
  add({ theorem: 'linear_growth_uniform_in_step', file: GG, assumptions: CL, claim: 'Безусловная трёхмерная регулярность — открытая задача тысячелетия; в ToS она помечена точно: между двумя показателями (квадратичной нелинейностью и тем, что было бы нужно для безусловного контроля) лежит зазор, который ни один известный приём не закрывает.[^6]',
    note: '«То, что было бы нужно для безусловного контроля» — линейный рост: ' + N_LIN });

  // сноска 1
  fix('`millennium_gap_precise` (`AttackSynthesis.v`, точная формулировка открытого зазора)', 'millennium_gap_precise', { claim: F1D, assumptions: CL,
    note: DONE + ': теорема названа сводом. ' + N_MGP });
  fix('Точные имена и счётчики — по `README`/`CLAUDE` репозитория.', 'README', { claim: F1Z, theorem: null, file: '', assumptions: '',
    note: DONE + ': отсылка к README/CLAUDE заменена числами. Счёт по src/navier_stokes на 23.11.2026: 39 файлов .v, 957 строк Qed. README.md каталога отстал («34 files | 654 Qed | 3 axioms»), как и строка CLAUDE.md («34 .v files, 869 Qed»).' });
  fix('Точные имена и счётчики — по `README`/`CLAUDE` репозитория.', 'CLAUDE', { claim: F1Z, theorem: null, file: '', assumptions: '',
    note: DONE + ': отсылка к README/CLAUDE заменена числами. Счёт по src/navier_stokes на 23.11.2026: 39 файлов .v, 957 строк Qed. README.md каталога отстал («34 files | 654 Qed | 3 axioms»), как и строка CLAUDE.md («34 .v files, 869 Qed»).' });

  // сноска 6
  fix('`millennium_gap_precise` (`AttackSynthesis.v`): точная формулировка зазора', 'millennium_gap_precise', { claim: F6A, theorem: 'linear_growth_uniform_in_step', file: GG, assumptions: CL,
    note: DONE + ': сноска переписана. ' + N_LIN });
  add({ theorem: 'quadratic_growth_subcritical', file: GG, assumptions: CL, claim: F6B, note: N_SUB });
  add({ theorem: 'quadratic_growth_not_uniform_in_step', file: GG, assumptions: CL, claim: F6B, note: N_SUP });
  add({ theorem: 'k_rate_unbounded', file: GG, assumptions: CL, claim: F6C, page_price: '0 аксиом', note: N_KR });
  add({ theorem: null, file: GG, claim: F6C, page_price: '0 аксиом', assumptions: ALL14,
    note: 'src/process/ProcessGrowthExponentGap.v: 12 Qed и два определения; строк Axiom, Parameter, Admitted нет.' });
  add({ theorem: 'millennium_gap_precise', file: AS, assumptions: CL, claim: F6D, note: N_MGP });
  add({ theorem: null, file: HA, claim: F6E,
    note: 'HonestAssessment.v: 26 теорем о положительности и сравнении чисел (например, not_solved, :339: (C_0 + A)^2 > A^2); что задача открыта, сказано в комментариях файла.' });
  add({ theorem: null, file: GG, claim: F6F,
    note: 'Верно: связи между энстрофией траектории gtraj и рекуррентами lin_iter, quad_iter в формализации нет; квадратичная оценка вытяжения в прежних файлах введена определением (stretching_enstrophy_bound, Vorticity.v:196).' });

  save();
}
