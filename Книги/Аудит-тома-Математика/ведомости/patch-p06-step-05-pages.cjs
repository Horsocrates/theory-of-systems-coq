// Часть VI, шаг 5, страницы (2026-11-15, слово автора «Да; продолжай»): 12 правок главы VI.5 внесены
// (определение ОН-системы и проекции, оговорка в формуле Бесселя, фраза о RealProcess; сноски 1, 3, 4, 5, 7–11).
// Формализация — новый src/process/ProcessL2Orthonormal.v; прежние файлы не менялись.
// Запуск: node patch-p06-step-05-pages.cjs  (затем relocate + merge по part06-ch05). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 15.11 (Часть VI, шаг 5, слово автора)';
const BYF = DONE + ' (формализацией; текст страницы не менялся)';
const CL = 'Closed under the global context';
const LO = 'src/process/ProcessL2Orthonormal.v';
const BG = 'src/process/ProcessL2BesselGeneral.v';
const PV = 'src/process/ProcessL2Parseval.v';
const CS = 'src/process/ProcessL2CauchySchwarz.v';
const BS = String.fromCharCode(92);
const L = (s) => s.split('§').join(BS);   // «§» — обратная косая черта
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

function open(name) {
  const p = path.join(__dirname, name + '.json');
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0, noted = 0;
  const pick = (prefix, th) => {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
    if (hit.length > 1) throw new Error(name + ': не одна запись: ' + prefix + ' / ' + th);
    return hit[0];
  };
  const fix = (prefix, th, fields) => { const r = pick(prefix, th); if (!r) return; Object.assign(r, { verdict: 'ok' }, fields); n++; };
  const note = (prefix, th, text) => {
    const r = pick(prefix, th);
    if (!r) throw new Error(name + ': запись для примечания не найдена: ' + prefix + ' / ' + th);
    if (r.note !== text) { r.note = text; noted++; }
  };
  const add = (rec) => {
    if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
    j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
  };
  const save = () => { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + '.json: изменено ' + n + ', примечаний ' + noted + ', добавлено ' + added + ', всего ' + j.records.length); };
  return { j, fix, note, add, save };
}

// утверждения нового файла (номера строк — src/process/ProcessL2Orthonormal.v)
const N_HON = 'Посылка раздела ONB (:189): Hypothesis Hon : forall i j, i < K0 -> j < K0 -> seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0) — ортонормированы первые K0 векторов семейства e на N координатах.';
const N_UNSAT = 'on_all_indices_unsat : forall (e : nat -> nat -> Q) (N : nat), ~ (forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)) (:134) — посылка «при всех номерах» невыполнима ни при каком N; стандартный базис ей не удовлетворяет (std_basis_fails_all_indices, :166). ' + CL + '.';
const N_RESID = 'resid_norm_b : forall K, K <= K0 -> ‖f − Σ_{k<K}⟨e_k,f⟩e_k‖² == ‖f‖² − Σ_{k<K}⟨e_k,f⟩² (:231); общее тождество для произвольных коэффициентов — gen_resid (:208). ' + N_HON + ' ' + CL + '.';
const N_BESSEL = 'bessel_b : forall K, K <= K0 -> q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K <= seq_inner f f N (:243). ' + N_HON + ' ' + CL + '.';
const N_BEST = 'best_approx_b : forall (a : nat -> Q) (K : nat), K <= K0 -> ‖f − Σ_{k<K}⟨e_k,f⟩e_k‖² <= ‖f − Σ_{k<K} a_k e_k‖² (:256) — для любых коэффициентов a. ' + CL + '.';
const N_ESPLIT = 'energy_split_b : forall K, K <= K0 -> Σ_{k<K}⟨e_k,f⟩² + ‖r_K‖² == ‖f‖² (:276). ' + CL + '.';
const N_PRZ = 'parseval_iff_resid_zero_b : forall K, K <= K0 -> (Σ_{k<K}⟨e_k,f⟩² == ‖f‖²) <-> (‖r_K‖² == 0) (:286). ' + CL + '.';
const N_PARS = 'parseval_iff_complete_b : forall K, K <= K0 -> (Σ_{k<K}⟨e_k,f⟩² == ‖f‖²) <-> (forall m, m < N -> Σ_{k<K}⟨e_k,f⟩·e_k(m) == f m) (:296). ' + N_HON + ' ' + CL + '.';
const N_PORT = 'proj_ortho_b : forall (coef : nat -> Q) (K : nat), K < K0 -> seq_inner (e K) (fun m => q_sum (fun k => coef k * e k m) K) N == 0 (:193). ' + CL + '.';
const N_STD = 'std_basis_on : forall N i j, i < N -> j < N -> seq_inner (delta i) (delta j) N == (if Nat.eqb i j then 1 else 0) (:323), где delta m — m-й вектор стандартного базиса (:74); следствия — bessel_std (:330), parseval_std_all (:337). ' + CL + '.';
const N_ROT = 'rot_orthonormal : forall i j, i < 2 -> j < 2 -> seq_inner (rot i) (rot j) 2 == (if Nat.eqb i j then 1 else 0) (:361), где rot 0 = (3/5, 4/5), rot 1 = (−4/5, 3/5) (:352); следствия — bessel_rot (:370), parseval_rot (:377). ' + CL + '.';
const N_PSTD = 'parseval_std_all : forall (f : nat -> Q) (N : nat), q_sum (fun k => seq_inner (delta k) f N * seq_inner (delta k) f N) N == seq_inner f f N (:337). ' + CL + '.';
const N_PROT = 'parseval_rot : forall f, q_sum (fun k => seq_inner (rot k) f 2 * seq_inner (rot k) f 2) 2 == seq_inner f f 2 (:377). ' + CL + '.';
const N_LAGR = 'lagrange_identity : forall (a b : nat -> Q) (N : nat), q_sum (fun j => q_sum (fun i => (a i * b j - a j * b i) * (a i * b j - a j * b i)) N) N == 2 * (q_sum (fun i => a i * a i) N * q_sum (fun i => b i * b i) N - q_sum (fun i => a i * b i) N * q_sum (fun i => a i * b i) N) (:397). ' + CL + '.';
const N_GAP = 'cs_gap_is_sum_of_squares (:412): ‖a‖²‖b‖² − ⟨a,b⟩² == (1/2)·Σ_j Σ_i (a_i b_j − a_j b_i)² — формула страницы. ' + CL + '.';
const N_CSL = 'cauchy_schwarz_via_lagrange (:422): ⟨a,b⟩² <= ‖a‖²‖b‖² — выведено из cs_gap_is_sum_of_squares и неотрицательности суммы квадратов. ' + CL + '.';
const N_L1L2 = 'l1_sq_le_N_l2_sq : forall (f : nat -> Q) (N : nat), q_sum (fun i => Qabs (f i)) N * q_sum (fun i => Qabs (f i)) N <= q_sum (fun i => f i * f i) N * inject_Z (Z.of_nat N) (:448) — из q_sum_cauchy_schwarz при втором аргументе 1. ' + CL + '.';
const N_POL = 'l2_polarization : forall f g pts w N, l2_inner f g pts w N == (1 # 2) * (l2_inner (fun x => f x + g x) (fun x => f x + g x) pts w N - l2_inner f f pts w N - l2_inner g g pts w N) (:465). ' + CL + '.';
const N_RO1 = 'resid_ortho_one : forall e f N, seq_inner e e N == 1 -> seq_inner e (fun m => f m - seq_inner e f N * e m) N == 0 (:477). ' + CL + '.';
const N_BA1 = 'best_approx_one : forall e f c N, seq_inner e e N == 1 -> ‖f − ⟨e,f⟩e‖² <= ‖f − c·e‖² (:487). ' + CL + '.';
const N_COORD = 'l2_limit_coord_is_Cauchy : forall (F : nat -> nat -> Q) (N : nat), L2CauchySq F N -> forall i, i < N -> is_Cauchy (l2_limit F i) (:530) — через sq_cauchy_is_Cauchy (:506): квадратичное условие Коши влечёт is_Cauchy (ProcessCore.v:68). ' + CL + '.';
const N_RF = 'riesz_fischer_process_form : forall F N, L2CauchySq F N -> (forall i, i < N -> is_Cauchy (l2_limit F i)) ' + '/' + BS + ' (forall n, is_Cauchy (dist_to_limit F N n)) ' + '/' + BS + ' (forall eps, eps > 0 -> exists M, forall n, M <= n -> exists S, forall s, S <= s -> dist_to_limit F N n s <= eps) (:618); dist_to_limit F N n s — квадрат расстояния от F n до стадии s предела (:547). ' + CL + '.';

{
  const { fix, note, add, save } = open('part06-ch05');

  // --- основной текст, не менялся (места 5.1, 5.2)
  fix('*Доказано без аксиом* (на конечном носителе из $N$ точек, на каждой стадии):', null, { theorem: 'bessel_b', file: LO,
    note: BYF + ': было — общее неравенство Бесселя и критерий Парсеваля доказаны под посылкой ортонормированности при всех номерах (невыполнима), наилучшее приближение в опорных файлах не записано. ' + N_BESSEL + ' ' + N_BEST + ' ' + N_PARS + ' Остальное из перечня — как сказано.' });
  fix('Оно говорит, что «косинус угла не больше единицы», и доказывается *точно, без аксиом*', 'sos_identity', { theorem: 'cs_gap_is_sum_of_squares', file: LO,
    note: BYF + ', сноска 4 переписана: было — тождества страницы в формализации не было (sos_identity — разложение одной суммы квадратов). ' + N_GAP + ' ' + N_CSL + ' ' + N_LAGR });
  fix('Сердцевина теории — *тождество нормы остатка*:', 'resid_norm', { theorem: 'resid_norm_b', file: LO,
    note: BYF + ', сноска 9 переписана: было — resid_norm под невыполнимой посылкой. ' + N_RESID });
  fix(L('Из неотрицательности $§|r_K§|^2§ge0$ немедленно следует *общее неравенство Бесселя*:'), 'bessel_general', { theorem: 'bessel_b', file: LO,
    note: DONE + ' (формализацией; в формуле добавлена оговорка K <= K0): было — bessel_general под невыполнимой посылкой. ' + N_BESSEL + ' Посылка выполнима: std_basis_on (:323), rot_orthonormal (:361).' });
  fix('*Равенство* в Бесселе — *равенство Парсеваля* — наступает ровно тогда, когда остаток исчезает:', 'parseval_iff_complete', { theorem: 'parseval_iff_complete_b', file: LO,
    note: BYF + ', сноска 10 переписана: было — parseval_iff_complete под невыполнимой посылкой. ' + N_PARS + ' ' + N_PRZ });
  fix('правила (Коши–Шварц, бескорневая дистанция, наилучшее приближение, Бессель, Парсеваль) доказаны на конечных стадиях без аксиом,', null, { theorem: 'best_approx_b', file: LO,
    note: BYF + ': ' + N_BEST + ' ' + N_BESSEL + ' ' + N_PARS });
  note(L('то есть энергия раскладывается на долю вдоль $e$ и энергию остатка, а остаток ортогонален $e$.'), null,
    'Разложение энергии — pythagoras_one (ProcessL2Bessel.v:69). «Остаток ортогонален e» — resid_ortho_one (' + LO + ':477, шаг 5; названа в сноске 8). ' + CL + '.');
  note('Строго: при фиксированном усечении на $N$ координат первые $K$ направлений *восстанавливают каждую координату* $m<N$.', null,
    'Соответствует правой части parseval_iff_complete_b (' + LO + ':296): forall m, m < N -> q_sum (fun k => seq_inner (e k) f N * e k m) K == f m. Оговорка о конечности стоит честно.');
  note('На конечной выборке из $N$ точек оба измеряют ту же функцию, и доказанное неравенство Коши–Шварца', null,
    'Неравенство (Σ|f_i|)² ≤ (Σ f_i²)·N — l1_sq_le_N_l2_sq (' + LO + ':448, шаг 5; названа в сноске 3): следствие q_sum_cauchy_schwarz при втором аргументе 1. ' + CL + '.');
  note(L('Отсюда: если $§{f_n§}$ есть Коши в $L^2$-норме, то *каждая координата*'), 'l2cauchy_coord_cauchy',
    'Lemma l2cauchy_coord_cauchy (ProcessL2RieszFischer.v:94): L2CauchySq F N -> для i < N и eps > 0 есть M: (F m i − F n i)² <= eps при m, n >= M — условие Коши для квадрата разности. В форме предиката is_Cauchy (ProcessCore.v:68) — l2_limit_coord_is_Cauchy (' + LO + ':530, шаг 5). ' + CL + '.');

  // --- правка 1: определение ОН-системы (место 5.1)
  fix(L('*Ортонормированная* (ОН) система — семейство $§{e_k§}$ с'), null, { file: LO,
    claim: L('*Ортонормированная* (ОН) система — конечное семейство $§{e_k§}_{k<K_0}$ с $§langle e_i,e_j§rangle=1$ при $i=j$ и $0$ иначе.'),
    note: DONE + ': было «семейство $' + BS + '{e_k' + BS + '}$» — в формализации посылка стояла для всех натуральных номеров и была невыполнима. ' + N_HON + ' ' + N_UNSAT });

  // --- правка 3: RealProcess (место 5.4)
  const C216 = L('А Коши-последовательность в ℚ — это в точности вещественное как процесс: `RealProcess` ($ℕ§toℚ$) с условием Коши `is_Cauchy`.');
  fix('А Коши-последовательность в ℚ — это в точности определение вещественного как процесса', 'RealProcess', { claim: C216,
    note: DONE + ': было «это в точности определение вещественного как процесса (`RealProcess`)» — тип RealProcess есть nat -> Q без условия Коши. Definition RealProcess := nat -> Q (ProcessCore.v:34); условие — предикат is_Cauchy (:68). Что координаты предела ему удовлетворяют — ' + N_COORD });
  add({ theorem: 'is_Cauchy', file: 'src/process/ProcessCore.v', claim: C216,
    note: 'Definition is_Cauchy (R : RealProcess) : Prop := forall eps, 0 < eps -> exists N, forall m n, N <= m -> N <= n -> Qabs (R m - R n) < eps (ProcessCore.v:68). ' + N_COORD });

  // --- правка 4: сноска 1
  fix('Опорные файлы каталога `src/process/` Rocq-репозитория ToS: `ProcessL2CauchySchwarz.v`,', null, {
    claim: 'Опорные файлы каталога `src/process/` Rocq-репозитория ToS: `ProcessL2CauchySchwarz.v`, `ProcessL2Triangle.v`, `ProcessL2Bessel.v`, `ProcessL2BesselGeneral.v`, `ProcessL2Parseval.v`, `ProcessL2RieszFischer.v`, `ProcessL2Orthonormal.v`; их связки — в `ProcessL2HilbertSynthesis.v`.',
    note: 'Все восемь файлов лежат в src/process/; ProcessL2Orthonormal.v добавлен 15.11 (шаг 5): 36 Qed, все объявления — ' + CL + '. В ProcessL2HilbertSynthesis.v три Qed — конъюнкции ранее доказанного; orthonormal_expansion_synthesis (:99) = bessel_general ∧ parseval_iff_complete под посылкой для всех номеров (невыполнима: on_all_indices_unsat) — на странице эта теорема не названа.' });

  // --- правка 5: сноска 3
  const C3 = L('Прямое следствие `q_sum_cauchy_schwarz` в `ProcessL2CauchySchwarz.v` (0 аксиом) с $g§equiv1$ — `l1_sq_le_N_l2_sq` (`ProcessL2Orthonormal.v`).');
  fix('Прямое следствие `q_sum_cauchy_schwarz` в `ProcessL2CauchySchwarz.v` (0 аксиом) с', 'q_sum_cauchy_schwarz', { claim: C3,
    note: 'Lemma q_sum_cauchy_schwarz (:65): для a b : nat -> Q и всякого N: (Σ_{i<N} a_i b_i)² <= (Σ a_i²)(Σ b_i²). ' + CL + '. Само следствие записано: l1_sq_le_N_l2_sq (' + LO + ':448).' });
  add({ theorem: 'l1_sq_le_N_l2_sq', file: LO, claim: C3, note: DONE + ' (добавлено): ' + N_L1L2 });

  // --- правка 6: сноска 4 (место 5.2)
  const C4a = '`q_sum_cauchy_schwarz` и `l2_cauchy_schwarz` в `ProcessL2CauchySchwarz.v` (0 аксиом); опорные факты — неотрицательность квадрата `q_sq_nonneg` и разложение суммы квадратов `sos_identity`.';
  const C4b = 'Тождество Лагранжа — `lagrange_identity`, в виде формулы выше — `cs_gap_is_sum_of_squares`, неравенство из него — `cauchy_schwarz_via_lagrange` (`ProcessL2Orthonormal.v`, 0 аксиом).';
  fix('`q_sum_cauchy_schwarz` и `l2_cauchy_schwarz` в `ProcessL2CauchySchwarz.v` (0 аксиом); опорные факты', 'q_sq_nonneg', { claim: C4a,
    note: 'Lemma q_sq_nonneg (:45): forall x : Q, 0 <= x * x. Одноимённые леммы есть ещё в четырёх файлах; глава называет этот. ' + CL + '.' });
  add({ theorem: 'sos_identity', file: CS, claim: C4a, page_price: '0 аксиом',
    note: DONE + ': было «тождество Лагранжа `sos_identity`». Lemma sos_identity (:50): q_sum (fun i => (a i * q - p * b i) * (a i * q - p * b i)) k == q * q * Σa_i² − 2 * p * q * Σa_i b_i + p * p * Σb_i² — разложение одной суммы квадратов при постоянных p, q; сноска теперь так её и называет. ' + CL + '.' });
  add({ theorem: 'lagrange_identity', file: LO, claim: C4b, page_price: '0 аксиом', note: DONE + ' (добавлено): ' + N_LAGR });
  add({ theorem: 'cs_gap_is_sum_of_squares', file: LO, claim: C4b, page_price: '0 аксиом', note: N_GAP });
  add({ theorem: 'cauchy_schwarz_via_lagrange', file: LO, claim: C4b, page_price: '0 аксиом', note: N_CSL });

  // --- правка 7: сноска 5
  const C5 = 'Симметрия `l2_inner_sym` и разложение квадрата нормы `l2_inner_expand` в `ProcessL2CauchySchwarz.v` (0 аксиом); поляризация — их прямое следствие (`l2_polarization`, `ProcessL2Orthonormal.v`).';
  fix('Симметрия `l2_inner_sym` и разложение квадрата нормы `l2_inner_expand` в `ProcessL2CauchySchwarz.v` (0 аксиом);', 'l2_inner_expand', { claim: C5,
    note: 'Lemma l2_inner_expand (:148): ⟨f+g,f+g⟩ == ⟨f,f⟩ + 2⟨f,g⟩ + ⟨g,g⟩. ' + CL + '. Формула поляризации записана: l2_polarization (' + LO + ':465).' });
  add({ theorem: 'l2_polarization', file: LO, claim: C5, note: DONE + ' (добавлено): ' + N_POL });

  // --- правка 8: сноска 7
  fix('ортогональность проекции — `proj_ortho`;', 'proj_ortho', { theorem: 'proj_ortho_b', file: LO,
    claim: 'ортогональность проекции — `proj_ortho_b` (`ProcessL2Orthonormal.v`);',
    note: DONE + ': было «`proj_ortho`» — лемма под посылкой для всех номеров (невыполнима). ' + N_PORT + ' ' + N_HON });

  // --- правка 9: сноска 8
  fix('`pythagoras_one` и `bessel_one` в `ProcessL2Bessel.v` (0 аксиом).', 'bessel_one', {
    claim: '`pythagoras_one` и `bessel_one` в `ProcessL2Bessel.v` (0 аксиом);' });
  const C8b = 'ортогональность остатка — `resid_ortho_one`, наименьшая норма остатка среди кратных $e$ — `best_approx_one` (`ProcessL2Orthonormal.v`, 0 аксиом).';
  add({ theorem: 'resid_ortho_one', file: LO, claim: C8b, page_price: '0 аксиом', note: DONE + ' (добавлено): ' + N_RO1 });
  add({ theorem: 'best_approx_one', file: LO, claim: C8b, page_price: '0 аксиом', note: N_BA1 });

  // --- правка 10: сноска 9
  const C9a = L('`bessel_b` в `ProcessL2Orthonormal.v` (0 аксиом): из тождества остатка `resid_norm_b` и неотрицательности суммы квадратов; посылка — ортонормированность первых $K_0$ векторов, $K§le K_0$.');
  const C9b = 'Наилучшее приближение — `best_approx_b`: проекция даёт наименьший остаток среди всех комбинаций первых $K$ векторов.';
  const C9c = 'Посылка выполнима: стандартный базис (`std_basis_on`) и повёрнутый рациональный базис $(3/5,4/5)$, $(-4/5,3/5)$ (`rot_orthonormal`).';
  const C9d = 'Прежние `bessel_general` и `resid_norm` (`ProcessL2BesselGeneral.v`) требуют ортонормированности при всех номерах $i,j$; на $N$ координатах такая посылка невыполнима (`on_all_indices_unsat`).';
  add({ theorem: 'bessel_b', file: LO, claim: C9a, page_price: '0 аксиом', note: DONE + ': было «`bessel_general` в `ProcessL2BesselGeneral.v`». ' + N_BESSEL });
  add({ theorem: 'resid_norm_b', file: LO, claim: C9a, page_price: '0 аксиом', note: N_RESID });
  add({ theorem: 'best_approx_b', file: LO, claim: C9b, note: DONE + ' (добавлено): ' + N_BEST });
  add({ theorem: 'std_basis_on', file: LO, claim: C9c, note: N_STD });
  add({ theorem: 'rot_orthonormal', file: LO, claim: C9c, note: N_ROT });
  add({ theorem: 'on_all_indices_unsat', file: LO, claim: C9d, note: N_UNSAT });
  add({ theorem: 'bessel_general', file: BG, claim: C9d,
    note: 'Theorem bessel_general (:175) — под посылкой Hon : forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0) (:119), для всех натуральных i, j; сноска это говорит. ' + CL + '.' });
  add({ theorem: 'resid_norm', file: BG, claim: C9d, note: 'Lemma resid_norm (:150) — под той же посылкой Hon (:119). ' + CL + '.' });

  // --- правка 11: сноска 10
  const P10 = '`parseval_iff_complete` в `ProcessL2Parseval.v` (0 аксиом): `energy_split`';
  const C10a = L('`parseval_iff_complete_b` в `ProcessL2Orthonormal.v` (0 аксиом): `energy_split_b` $§sum c_k^2+§|r_K§|^2=§|f§|^2$, `parseval_iff_resid_zero_b`,');
  const C10b = 'Равенство достигается на стандартном базисе при всяком $N$ и всякой $f$ — `parseval_std_all` — и на повёрнутом базисе — `parseval_rot`; частный свидетель — `parseval_std_concrete`.';
  fix(P10, 'energy_split', { theorem: 'energy_split_b', file: LO, claim: C10a,
    note: DONE + ': было «`energy_split`» под невыполнимой посылкой. ' + N_ESPLIT });
  fix(P10, 'parseval_iff_resid_zero', { theorem: 'parseval_iff_resid_zero_b', file: LO, claim: C10a,
    note: DONE + ': было «`parseval_iff_resid_zero`» под невыполнимой посылкой. ' + N_PRZ });
  add({ theorem: 'parseval_iff_complete_b', file: LO, claim: C10a, page_price: '0 аксиом', note: N_PARS });
  add({ theorem: 'q_sum_sq_zero', file: PV, page_price: '0 аксиом',
    claim: L('и лемма `q_sum_sq_zero` из `ProcessL2Parseval.v` (сумма квадратов нулевая $§Rightarrow$ каждое слагаемое нулевое, через целостность умножения в ℚ).'),
    note: 'Lemma q_sum_sq_zero (:52): Σ_{i<N} g_i² == 0 -> forall i < N, g i == 0 (через Qmult_integral); посылки ортонормированности у леммы нет. ' + CL + '.' });
  fix('Конкретный свидетель достижимости равенства — `parseval_std_concrete` (стандартный базис).', 'parseval_std_concrete', { claim: C10b,
    note: 'Example parseval_std_concrete (ProcessL2Parseval.v:156): стандартный базис, N = 2, K = 2, f = (3, 4): 25 = 25, доказано vm_compute. Общий случай — parseval_std_all. ' + CL + '.' });
  add({ theorem: 'parseval_std_all', file: LO, claim: C10b, note: DONE + ' (добавлено): ' + N_PSTD });
  add({ theorem: 'parseval_rot', file: LO, claim: C10b, note: N_PROT });

  // --- правка 12: сноска 11
  const C11 = 'Что каждая координата предела есть процесс Коши (`is_Cauchy`) — `l2_limit_coord_is_Cauchy`; трёхчастная форма (координаты предела — процессы Коши; расстояние от $f_n$ до предела — процесс Коши; оно стремится к нулю) — `riesz_fischer_process_form` (`ProcessL2Orthonormal.v`, 0 аксиом).';
  add({ theorem: 'l2_limit_coord_is_Cauchy', file: LO, claim: C11, page_price: '0 аксиом', note: DONE + ' (добавлено): ' + N_COORD });
  add({ theorem: 'riesz_fischer_process_form', file: LO, claim: C11, page_price: '0 аксиом', note: N_RF });

  save();
}
