// Часть VII, шаг 1, страницы (2026-11-18, слово автора «Продолжай» на готовые «было — стало»): 24 правки глав
// VII.1 (15) и VII.4 (9) внесены; глава VII.5 слов не меняет (место 5.4 закрыто формализацией).
// Формализация — новый src/process/ProcessOrthonormalFourier.v поверх ProcessL2Orthonormal.v; прежние файлы не менялись.
// Запуск: node patch-p07-step-01-pages.cjs  (затем relocate + merge по part07-ch01, ch04, ch05). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 18.11 (Часть VII, шаг 1, слово автора)';
const BYF = DONE + ' (формализацией; текст страницы не менялся)';
const CL = 'Closed under the global context';
const PO = 'src/process/ProcessOrthonormalFourier.v';
const LO = 'src/process/ProcessL2Orthonormal.v';
const BS = String.fromCharCode(92);
const L = (s) => s.split('§').join(BS);   // «§» — обратная косая черта
const AND = '/' + BS;
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

function open(name) {
  const p = path.join(__dirname, name + '.json');
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  // th: undefined — любая теорема; null — запись без теоремы; строка — имя. file (необязательно) — уточнение.
  const pick = (prefix, th, file) => {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix)
      && (th === undefined || (th === null ? !r.theorem : r.theorem === th))
      && (file === undefined || r.file === file));
    if (hit.length > 1) throw new Error(name + ': не одна запись: ' + prefix + ' / ' + th);
    return hit[0];
  };
  const fix = (prefix, th, fields, file) => { const r = pick(prefix, th, file); if (!r) return; Object.assign(r, { verdict: 'ok' }, fields); n++; };
  const add = (rec) => {
    if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && r.file === rec.file && norm(r.claim) === norm(rec.claim))) return;
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

// --- утверждения (номера строк — по файлам PO и LO)
const PREM = 'Посылка раздела — ортонормированность первых K0 векторов: forall i j, i < K0 -> j < K0 -> seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0); теоремы — при K <= K0. Посылка выполнима: std_basis_on (ProcessL2Orthonormal.v:323), rot_orthonormal (:361).';
const N_BESSEL = 'bessel_b : K <= K0 -> q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K <= seq_inner f f N (ProcessL2Orthonormal.v:243). ' + PREM + ' ' + CL + '.';
const N_PROJ = 'proj_ortho_b : K < K0 -> seq_inner (e K) (fun m => q_sum (fun k => coef k * e k m) K) N == 0 (ProcessL2Orthonormal.v:193). ' + PREM + ' ' + CL + '.';
const N_RESO = 'resid_ortho_b : j < K -> K <= K0 -> seq_inner (e j) (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N == 0 (:138); через proj_coord_b : j < K -> K <= K0 -> seq_inner (e j) (fun m => q_sum (fun k => coef k * e k m) K) N == coef j (:125). ' + PREM + ' ' + CL + '.';
const N_COEF = 'coef_e_resid_b : K < K0 -> seq_inner (e K) (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N == seq_inner (e K) f N (:149). ' + PREM + ' ' + CL + '.';
const N_RESN = 'resid_norm_b : K <= K0 -> ‖f − P_K‖² == seq_inner f f N - q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K (ProcessL2Orthonormal.v:231); частный случай gen_resid (:208, произвольные веса; индукция по K). ' + PREM + ' ' + CL + '.';
const N_BEQ = 'best_approx_eq_b : K <= K0 -> ‖f − Σ_{k<K} a_k e_k‖² == ‖f − P_K‖² + q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K (:161). ' + PREM + ' ' + CL + '.';
const N_BUN = 'best_approx_unique_b : K <= K0 -> (‖f − Σ_{k<K} a_k e_k‖² == ‖f − P_K‖²) <-> (forall k, k < K -> a k == seq_inner (e k) f N) (:178); из best_approx_eq_b (:161) и q_sum_sq_zero. ' + PREM + ' ' + CL + '.';
const N_BGE = 'best_approx_b : K <= K0 -> ‖f − P_K‖² <= ‖f − Σ_{k<K} a_k e_k‖² для любых весов a (ProcessL2Orthonormal.v:256). ' + PREM + ' ' + CL + '.';
const N_SPLIT = 'energy_split_b : K <= K0 -> Σ_{k<K} c_k² + ‖f − P_K‖² == seq_inner f f N (ProcessL2Orthonormal.v:276). ' + PREM + ' ' + CL + '.';
const N_PRZ = 'parseval_iff_resid_zero_b : K <= K0 -> (Σ_{k<K} c_k² == seq_inner f f N) <-> (‖f − P_K‖² == 0) (ProcessL2Orthonormal.v:286). ' + PREM + ' ' + CL + '.';
const N_PIC = 'parseval_iff_complete_b : K <= K0 -> (Σ_{k<K} c_k² == seq_inner f f N) <-> (forall m, m < N -> q_sum (fun k => seq_inner (e k) f N * e k m) K == f m) (ProcessL2Orthonormal.v:296). ' + PREM + ' ' + CL + '.';
const N_CNT = 'on_count_le_dim : forall e N K0, (forall i j, i < K0 -> j < K0 -> seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)) -> K0 <= N (:208). ' + CL + '.';
const N_34 = 'parseval_3_4_from_criterion (:246): для f = (3, 4) и стандартного базиса двух координат — равенство Парсеваля (из parseval_std_all, ProcessL2Orthonormal.v:337) ' + AND + ' forall m, m < 2 -> q_sum (fun k => seq_inner (delta k) f 2 * delta k m) 2 == f m (по критерию parseval_iff_complete_b, :296 того же файла, с посылкой std_basis_on). ' + CL + '.';
const N_FULL = 'full_on_recovers : (forall i j, i < N -> j < N -> seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)) -> forall f m, m < N -> q_sum (fun k => seq_inner (e k) f N * e k m) N == f m (:469); full_on_parseval (:491): Σ_{k<N} c_k² == seq_inner f f N для всякой f; через full_on_column_norm (:415) и full_on_dual (:450). ' + CL + '.';
const N_STD = 'std_basis_on : forall N i j, i < N -> j < N -> seq_inner (delta i) (delta j) N == (if Nat.eqb i j then 1 else 0) (ProcessL2Orthonormal.v:323); rot_orthonormal (:361): базис (3/5, 4/5), (−4/5, 3/5) на двух координатах. ' + CL + '.';
const N_UNSAT = 'on_all_indices_unsat : forall e N, ~ (forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)) (ProcessL2Orthonormal.v:134). ' + CL + '.';
const N_BIL = 'seq_inner_bilinear_symmetric (:99): симметрия, линейность по второму и по первому аргументу; seq_inner_lin_r (:83), seq_inner_lin_l (:91) — индукция по N и ring. ' + CL + '.';
const N_ERR = 'fourier_error_eq_b : K <= K0 -> ferr e f N K == seq_inner f f N - captured (fun k => seq_inner (e k) f N) K (:294); ferr e f N K (:264) — ‖f − P_K‖²; из resid_norm_b (ProcessL2Orthonormal.v:231). ' + PREM + ' ' + CL + '.';
const N_NN = 'ferr_nonneg : forall e f N K, 0 <= ferr e f N K (:269) — посылки не берёт (сумма квадратов). ' + CL + '.';
const N_BFE = 'bessel_from_error_b : K <= K0 -> captured (fun k => seq_inner (e k) f N) K <= seq_inner f f N (:307) — из ferr_nonneg (:269) и fourier_error_eq_b (:294). ' + PREM + ' ' + CL + '.';
const N_STEP = 'fourier_error_step_b : S K <= K0 -> ferr e f N (S K) == ferr e f N K - seq_inner (e K) f N * seq_inner (e K) f N (:315). ' + PREM + ' ' + CL + '.';
const N_MONO = "fourier_error_monotone_b : K <= K' -> K' <= K0 -> ferr e f N K' <= ferr e f N K (:326); из fourier_error_eq_b и captured_mono (ProcessFourierCompression.v:49). " + PREM + ' ' + CL + '.';
const N_ZI = 'fourier_error_zero_iff_b : K <= K0 -> ferr e f N K == 0 <-> captured (fun k => seq_inner (e k) f N) K == seq_inner f f N (:337). ' + PREM + ' ' + CL + '.';
const N_ZR = 'fourier_error_zero_iff_recovers_b : K <= K0 -> ferr e f N K == 0 <-> (forall m, m < N -> q_sum (fun k => seq_inner (e k) f N * e k m) K == f m) (:344); из fourier_error_zero_iff_b (:337) и parseval_iff_complete_b (ProcessL2Orthonormal.v:296). ' + PREM + ' ' + CL + '.';
const N_PB = 'fourier_partial_best_b : K <= K0 -> ferr e f N K <= ‖f − Σ_{k<K} a_k e_k‖² для любых весов a (:357); то же, что best_approx_b (ProcessL2Orthonormal.v:256). ' + PREM + ' ' + CL + '.';
const N_TAIL = 'fourier_error_is_tail_b : K <= K0 -> captured cf K0 == seq_inner f f N -> ferr e f N K == q_sum (fun i => seq_inner (e (K + i)) f N * seq_inner (e (K + i)) f N) (K0 - K) (:365). ' + PREM + ' ' + CL + '.';
const N_END = "fourier_truncation_ends_exactly : (forall i j, i < N -> j < N -> seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)) -> forall f, ferr e f N 0 == seq_inner f f N " + AND + " (forall K K', K <= K' -> K' <= N -> ferr e f N K' <= ferr e f N K) " + AND + ' ferr e f N N == 0 (:500); std_truncation_ends_exactly (:516): ferr delta f N N == 0; rot_truncation_ends_exactly (:524). ' + CL + '.';
const N_FAIL = 'monotone_fails_without_on (:277): для семейства e_0 = (2) и f = (1) на одной координате ferr … 0 < ferr … 1 (1 < 9) — без ортонормированности ошибка растёт. ' + CL + '.';

// ================= Глава VII.1 =================
{
  const { fix, add, save } = open('part07-ch01');
  // --- текст страницы
  fix('Глава работает с *конечной* ортонормированной системой', 'bessel_general', { theorem: 'bessel_b', file: LO,
    note: BYF + ': названные утверждения доказаны под выполнимой посылкой — proj_ortho_b (:193), resid_norm_b (:231), bessel_b (:243), energy_split_b (:276), parseval_iff_complete_b (:296) в ProcessL2Orthonormal.v; resid_ortho_b (ProcessOrthonormalFourier.v:138). ' + PREM + ' Прежние теоремы (ProcessL2BesselGeneral.v, ProcessL2Parseval.v) стоят под посылкой при всех номерах, невыполнимой (on_all_indices_unsat). ' + CL + '.' });
  fix('*Первый* — конечная ортонормированная система на $N$ координатах', 'parseval_iff_complete', { theorem: 'parseval_iff_complete_b', file: LO,
    note: BYF + ': ' + N_PIC + ' Бессель — bessel_b (:243), тождество энергии — energy_split_b (:276).' });
  fix('В коде это *гипотеза* `Hon` раздела об ортонормированных системах — явно предъявленное условие на конкретный набор', 'Hon', {
    theorem: 'on_count_le_dim', file: PO,
    claim: L('В коде это *гипотеза* `Hon` раздела об ортонормированных системах — явно предъявленное условие на первые $K_0$ векторов конкретного набора $e$, а не существование «какого-то базиса».[^4] Таких векторов на $N$ координатах не больше $N$ (доказано: $K_0§le N$), и всюду ниже $K§le K_0$. Система конечна и рациональна; никакого завершённого бесконечного базиса здесь нет и не требуется.'),
    note: DONE + ': было «условие на конкретный набор e» — посылка при всех номерах i, j, невыполнимая (on_all_indices_unsat). Теперь условие — на первые K0 векторов. ' + N_CNT + ' ' + N_STD });
  fix('Сначала промежуточное: $K$-й вектор ортогонален оболочке первых $K$', 'proj_ortho', { theorem: 'proj_ortho_b', file: LO, note: BYF + ': ' + N_PROJ });
  fix('Следствие: для всех уже снятых направлений', 'resid_ortho', { theorem: 'resid_ortho_b', file: PO, note: BYF + ' (имя теперь названо в сноске 6): ' + N_RESO });
  fix('Это *теорема Пифагора* для ортогонального разложения', 'resid_norm', { theorem: 'resid_norm_b', file: LO, note: BYF + ': ' + N_RESN });
  fix('и это *доказанное тождество*, а не эвристика', 'best_approx_unique', { theorem: 'best_approx_unique_b', file: PO, note: BYF + ': ' + N_BUN });
  add({ theorem: 'best_approx_eq_b', file: PO, claim: L('и это *доказанное тождество*, а не эвристика: правая часть не меньше $§norm{f-P_K}^2$, с равенством тогда и только тогда, когда $a_k = c_k$ для всех $k<K$ — коэффициенты Фурье суть *единственный* минимум.[^8]'), note: N_BEQ });
  fix('Энергия, захваченная любым числом $K$ направлений', 'bessel_general', { theorem: 'bessel_b', file: LO,
    claim: L('Энергия, захваченная любым числом $K§le K_0$ направлений, не превосходит полной энергии функции.[^9]'),
    note: DONE + ': было «любым числом K направлений»; ортонормированных векторов на N координатах не больше N (on_count_le_dim, ProcessOrthonormalFourier.v:208). ' + N_BESSEL });
  fix('Полная энергия функции в точности делится', 'energy_split', { theorem: 'energy_split_b', file: LO, note: BYF + ': ' + N_SPLIT });
  fix('Расщепление энергии превращает его в точную эквивалентность', 'parseval_iff_resid_zero', { theorem: 'parseval_iff_resid_zero_b', file: LO, note: BYF + ': ' + N_PRZ });
  fix('Это и есть честное конструктивное содержание формулы', 'parseval_iff_complete', { theorem: 'parseval_iff_complete_b', file: LO, note: BYF + ': ' + N_PIC });
  fix('Чтобы критерий не остался пустым', 'parseval_std_concrete', { theorem: 'parseval_3_4_from_criterion', file: PO,
    note: BYF + ' (сноска 12 переписана): свидетель привязан к критерию. ' + N_34 + ' Само равенство 25 = 25 — parseval_std_concrete (ProcessL2Parseval.v:156).' });
  const C266 = 'Доказано конечное: критерий полноты на $N$ координатах и полнота всякой системы из $N$ ортонормированных векторов — при $K=N$ разложение восстанавливает любую $f$.';
  fix('Доказано конечное: критерий полноты на $N$ координатах.', 'parseval_iff_complete', { theorem: 'parseval_iff_complete_b', file: LO, claim: C266,
    note: DONE + ' (добавлена полнота системы из N векторов): ' + N_PIC });
  add({ theorem: 'full_on_recovers', file: PO, claim: C266, note: N_FULL });
  fix('Всё предыдущее говорилось об *абстрактной* ортонормированной системе', 'Hon', { theorem: 'std_basis_on', file: LO,
    note: DONE + ' (следом добавлена фраза о простейших примерах): условию с границей K0 удовлетворяют стандартный и повёрнутый базисы. ' + N_STD });
  add({ theorem: 'rot_orthonormal', file: LO, claim: 'Простейшие предъявлены сразу: стандартный базис и повёрнутый рациональный базис $(3/5,4/5)$, $(-4/5,3/5)$ удовлетворяют `Hon`.', note: N_STD });
  // --- сноска 1
  fix('Опорные файлы — `ProcessL2BesselGeneral.v` (каталог', null, { file: LO, page_price: '0 аксиом',
    claim: L('Опорные файлы (каталог `src/process/` Rocq-репозитория ToS) — `ProcessL2Orthonormal.v` (36 доказанных утверждений) и `ProcessOrthonormalFourier.v` (30); оба — 0 `Admitted`, 0 аксиом.'),
    note: DONE + ': в ProcessL2Orthonormal.v 36 строк Qed, в ProcessOrthonormalFourier.v — 30; Admitted, Axiom, Parameter в них нет; все объявления — ' + CL + '.' });
  add({ theorem: 'on_count_le_dim', file: PO, page_price: '', claim: L('В них условие ортонормированности наложено на первые $K_0$ векторов системы, а теоремы доказаны для $K§le K_0$.'), note: PREM + ' ' + N_CNT });
  fix('Имена лемм в сносках ниже — из них и из `ProcessFourierON.v`.', null, { claim: 'Имена лемм в сносках ниже — из этих файлов и из `ProcessFourierON.v`.' });
  // --- сноска 3
  fix('`seq_inner_sym` (симметрия) и `seq_inner_sub_r`', 'seq_inner_sub_r', {
    claim: '`seq_inner_sym` (симметрия) и `seq_inner_sub_r` (линейность по разности во втором аргументе) в `ProcessL2BesselGeneral.v`;' });
  add({ theorem: 'seq_inner_bilinear_symmetric', file: PO, page_price: '0 аксиом',
    claim: 'линейность по каждому аргументу в общем виде — `seq_inner_lin_r`, `seq_inner_lin_l`, сводно — `seq_inner_bilinear_symmetric` в `ProcessOrthonormalFourier.v` (индукция по $N$ и `ring`). Все — 0 аксиом.', note: N_BIL });
  for (const th of ['seq_inner_lin_r', 'seq_inner_lin_l']) add({ theorem: th, file: PO, page_price: '0 аксиом',
    claim: 'линейность по каждому аргументу в общем виде — `seq_inner_lin_r`, `seq_inner_lin_l`, сводно — `seq_inner_bilinear_symmetric` в `ProcessOrthonormalFourier.v` (индукция по $N$ и `ring`). Все — 0 аксиом.', note: N_BIL });
  // --- сноска 4
  fix('`Hypothesis Hon : forall i j, seq_inner (e i) (e j) N', 'Hon', { file: LO,
    claim: '`Hypothesis Hon : forall i j, (i < K0)%nat -> (j < K0)%nat -> seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)` в `ProcessL2Orthonormal.v` и `ProcessOrthonormalFourier.v`.',
    note: DONE + ': посылка разделов ONB (ProcessL2Orthonormal.v:189), OrthonormalResidual, FourierError (ProcessOrthonormalFourier.v) — дословно.' });
  const C4B = L('Условию удовлетворяют стандартный базис (`std_basis_on`) и повёрнутый рациональный базис $(3/5,4/5)$, $(-4/5,3/5)$ (`rot_orthonormal`); $K_0§le N$ — `on_count_le_dim`.');
  add({ theorem: 'std_basis_on', file: LO, claim: C4B, note: N_STD });
  add({ theorem: 'on_count_le_dim', file: PO, claim: C4B, note: N_CNT });
  fix('Конкретная система, удовлетворяющая `Hon` (нормированный Уолш)', 'on_all_indices_unsat', {
    claim: 'В `ProcessL2BesselGeneral.v`, `ProcessL2Parseval.v` и `ProcessBestApproximation.v` то же условие записано для всех номеров $i,j$; на $N$ координатах оно невыполнимо (`on_all_indices_unsat`), и теоремы под ним примеров не имеют.',
    note: DONE + ': было «Конкретная система, удовлетворяющая Hon (нормированный Уолш)» — такой системы нет. ' + N_UNSAT });
  // --- сноска 6
  add({ theorem: 'proj_ortho_b', file: LO, claim: L('`proj_ortho_b` (`ProcessL2Orthonormal.v`): $§inner{e_K}{§sum_{k<K} c_k e_k}_N = 0$ при $K<K_0$.'), note: N_PROJ });
  fix('Отсюда `coef_e_resid`:', 'coef_e_resid', { theorem: 'coef_e_resid_b', file: PO,
    claim: L('Отсюда `coef_e_resid_b`: $§inner{e_K}{f-P_K}_N = §inner{e_K}{f}_N$ — проекция не трогает ещё не снятую координату.'),
    note: DONE + ': ' + N_COEF });
  add({ theorem: 'resid_ortho_b', file: PO, page_price: '0 аксиом',
    claim: L('Ортогональность остатка снятым направлениям, $§inner{e_j}{r_K}_N=0$ при $j<K§le K_0$, — `resid_ortho_b` (через `proj_coord_b`: $§inner{e_j}{§sum_{k<K} c_k e_k}_N=c_j$). Последние три — в `ProcessOrthonormalFourier.v`; все — 0 аксиом.'), note: N_RESO });
  add({ theorem: 'proj_coord_b', file: PO, page_price: '0 аксиом',
    claim: L('Ортогональность остатка снятым направлениям, $§inner{e_j}{r_K}_N=0$ при $j<K§le K_0$, — `resid_ortho_b` (через `proj_coord_b`: $§inner{e_j}{§sum_{k<K} c_k e_k}_N=c_j$). Последние три — в `ProcessOrthonormalFourier.v`; все — 0 аксиом.'), note: N_RESO });
  // --- сноска 7
  const C7 = L('`resid_norm_b` в `ProcessL2Orthonormal.v` ($K§le K_0$): частный случай общего тождества остатка для произвольных весов `gen_resid`, которое доказывается индукцией по $K$ через тождество $§norm{F-cE}^2 = §norm{F}^2 - 2c§inner{E}{F} + c^2§norm{E}^2$ (`seq_inner_resid`) и ортогональность проекции `proj_ortho_b`. 0 аксиом.');
  fix('`resid_norm` в `ProcessL2BesselGeneral.v`: доказывается индукцией', 'seq_inner_resid', { claim: C7 });
  add({ theorem: 'resid_norm_b', file: LO, page_price: '0 аксиом', claim: C7, note: N_RESN });
  add({ theorem: 'gen_resid', file: LO, page_price: '0 аксиом', claim: C7, note: N_RESN });
  // --- сноска 8
  fix('Тождество наилучшего приближения — `best_approx_eq`;', 'best_approx_eq', { theorem: 'best_approx_eq_b', file: PO,
    claim: 'Тождество наилучшего приближения — `best_approx_eq_b`;', note: DONE + ': ' + N_BEQ });
  fix('следствие-минимум', 'best_approx_ge', { theorem: 'best_approx_b', file: LO,
    claim: L('Следствие-минимум $§norm{f-P_K}^2§le§norm{f-§sum a_k e_k}^2$ — `best_approx_b` в `ProcessL2Orthonormal.v`.'), note: DONE + ': ' + N_BGE });
  fix(L('единственность (равенство $§Leftrightarrow$ $a_k=c_k$) —'), 'best_approx_unique', { theorem: 'best_approx_unique_b', file: PO,
    claim: L('единственность (равенство $§Leftrightarrow$ $a_k=c_k$ при $k<K$) — `best_approx_unique_b` (через лемму «конечная сумма квадратов над ℚ равна нулю лишь когда каждое слагаемое нуль», `q_sum_sq_zero`); обе — в `ProcessOrthonormalFourier.v`.'),
    note: DONE + ': ' + N_BUN });
  // --- сноска 9
  fix('`bessel_general` в `ProcessL2BesselGeneral.v`: из `resid_norm`', 'lra', {
    claim: L('`bessel_b` в `ProcessL2Orthonormal.v` ($K§le K_0$): из `resid_norm_b` и неотрицательности нормы остатка одним шагом `lra`. 0 аксиом.') });
  fix('Это общее неравенство Бесселя для произвольной конечной ортонормированной системы', 'bessel_general', { theorem: 'bessel_b', file: LO, note: BYF + ' (имя в сноске заменено): ' + N_BESSEL });
  // --- сноски 10–13
  add({ theorem: 'energy_split_b', file: LO, page_price: '0 аксиом', claim: L('`energy_split_b` в `ProcessL2Orthonormal.v` ($K§le K_0$): прямое следствие `resid_norm_b` (переписывание и `ring`). 0 аксиом.'), note: N_SPLIT });
  add({ theorem: 'parseval_iff_complete_b', file: LO, page_price: '0 аксиом', claim: L('`parseval_iff_complete_b` в `ProcessL2Orthonormal.v` ($K§le K_0$); опирается на `q_sum_sq_zero` («сумма квадратов нуль $§Rightarrow$ каждый член нуль» над ℚ) и тождество остатка `resid_norm_b`; промежуточная эквивалентность «Парсеваль $§Leftrightarrow$ нулевая норма остатка» — `parseval_iff_resid_zero_b`. 0 аксиом.'), note: N_PIC });
  add({ theorem: 'parseval_3_4_from_criterion', file: PO, claim: '`parseval_3_4_from_criterion` в `ProcessOrthonormalFourier.v`: стандартный базис удовлетворяет `Hon` (`std_basis_on`), равенство Парсеваля для него выполнено при всяком $N$ и всякой $f$ (`parseval_std_all`), и по критерию `parseval_iff_complete_b` разложение восстанавливает обе координаты $f=(3,4)$.', note: N_34 });
  add({ theorem: 'parseval_std_all', file: LO, claim: '`parseval_3_4_from_criterion` в `ProcessOrthonormalFourier.v`: стандартный базис удовлетворяет `Hon` (`std_basis_on`), равенство Парсеваля для него выполнено при всяком $N$ и всякой $f$ (`parseval_std_all`), и по критерию `parseval_iff_complete_b` разложение восстанавливает обе координаты $f=(3,4)$.',
    note: 'parseval_std_all : forall f N, q_sum (fun k => seq_inner (delta k) f N * seq_inner (delta k) f N) N == seq_inner f f N (ProcessL2Orthonormal.v:337). ' + CL + '.' });
  add({ theorem: 'parseval_std_concrete', file: 'src/process/ProcessL2Parseval.v', claim: "Само равенство $25=25$ — `parseval_std_concrete` в `ProcessL2Parseval.v`: проверяется `vm_compute`'ом — точной рациональной арифметикой.",
    note: 'parseval_std_concrete (ProcessL2Parseval.v:156): для стандартного базиса двух координат и f = (3, 4) сумма квадратов коэффициентов равна seq_inner f f 2 (25 = 25); пример вне раздела ON, посылки Hon не берёт. ' + CL + '.' });
  add({ theorem: 'full_on_recovers', file: PO, page_price: '0 аксиом', claim: 'Критерий — `parseval_iff_complete_b`; полнота системы из $N$ ортонормированных векторов — `full_on_recovers` и `full_on_parseval` (`ProcessOrthonormalFourier.v`), 0 аксиом.', note: N_FULL });
  add({ theorem: 'full_on_parseval', file: PO, page_price: '0 аксиом', claim: 'Критерий — `parseval_iff_complete_b`; полнота системы из $N$ ортонормированных векторов — `full_on_recovers` и `full_on_parseval` (`ProcessOrthonormalFourier.v`), 0 аксиом.', note: N_FULL });
  save();
}

// ================= Глава VII.4 =================
{
  const { fix, add, save } = open('part07-ch04');
  const FS = 'src/process/ProcessFourierSeriesL2.v', BA = 'src/process/ProcessBestApproximation.v';
  // --- текст страницы
  fix('Доказано над ℚ следующее (для конечной ортонормированной системы', null, { theorem: 'fourier_error_eq_b', file: PO, assumptions: CL,
    note: BYF + ' (сноска 1 переписана): утверждения перечня доказаны под выполнимой посылкой в ProcessOrthonormalFourier.v — fourier_error_eq_b (:294), ferr_nonneg (:269), fourier_error_monotone_b (:326), fourier_partial_best_b (:357), fourier_error_zero_iff_recovers_b (:344). ' + PREM + ' ' + CL + '.' });
  fix('Квадрат ошибки усечения равен полной энергии минус захваченная', 'fourier_error_eq', { theorem: 'fourier_error_eq_b', file: PO, note: BYF + ': ' + N_ERR });
  fix('эта ошибка неотрицательна (Бессель) и *монотонно убывает*', 'fourier_error_monotone', { theorem: 'fourier_error_monotone_b', file: PO, note: BYF + ': ' + N_MONO + ' Неотрицательность — ferr_nonneg (:269).' });
  fix('частичная сумма $P_K$ — наилучшее $K$-членное приближение;', 'fourier_partial_best', { theorem: 'fourier_partial_best_b', file: PO, note: BYF + ': ' + N_PB });
  fix('а ошибка обращается в нуль тогда и только тогда', 'fourier_error_zero_iff', { theorem: 'fourier_error_zero_iff_recovers_b', file: PO, note: BYF + ': обе половины фразы — ' + N_ZI + ' ' + N_ZR });
  fix('*Первый* — конечная теория усечений', null, { theorem: 'fourier_truncation_ends_exactly', file: PO, assumptions: CL,
    note: BYF + ': ошибка = полная − захваченная (fourier_error_eq_b, :294), хвост (fourier_error_is_tail_b, :365), монотонность (:326), наилучшее приближение (:357), критерий (:344). ' + N_END });
  fix('Неравенство Бесселя (Глава 7.1) даёт *энергетический бюджет*:', 'bessel_general', { theorem: 'bessel_b', file: LO, note: BYF + ': ' + N_BESSEL });
  fix('В конечном усечении на $N$ координатах это проверяется конечным критерием', 'fourier_error_zero_iff', { theorem: 'fourier_truncation_ends_exactly', file: PO, note: BYF + ': ' + N_END + ' Критерий — ' + N_ZR });
  fix('Квадрат ошибки усечения *в точности* равен отброшенной хвостовой энергии', 'fourier_error_eq', { theorem: 'fourier_error_eq_b', file: PO, note: BYF + ': ' + N_ERR + ' В виде суммы квадратов отброшенных коэффициентов — ' + N_TAIL });
  fix('*Неотрицательность.* Ошибка', 'bessel_general', { theorem: 'bessel_from_error_b', file: PO, note: BYF + ' (сноска 4 переписана): ' + N_NN + ' ' + N_BFE });
  fix('*Монотонное убывание.*', 'fourier_error_monotone', { theorem: 'fourier_error_monotone_b', file: PO, note: BYF + ': ' + N_MONO + ' ' + N_STEP });
  fix('среди всех $K$-членных линейных комбинаций системы', 'best_approx_unique', { theorem: 'best_approx_unique_b', file: PO, note: BYF + ': ' + N_BUN + ' Минимальность — ' + N_PB });
  fix('Поэтому процесс усечения не просто убывает', 'fourier_partial_best', { theorem: 'fourier_partial_best_b', file: PO, note: BYF + ': ' + N_PB + ' «На каждом K» — при K <= K0 <= N (on_count_le_dim, :208).' });
  fix('Когда же ошибка достигает нуля?', 'fourier_error_zero_iff', { theorem: 'fourier_error_zero_iff_recovers_b', file: PO, note: BYF + ': ' + N_ZI + ' ' + N_ZR });
  fix('Это конечный критерий полноты Главы 7.1, прочитанный как критерий сходимости', 'parseval_iff_complete', { theorem: 'parseval_iff_complete_b', file: LO,
    note: BYF + ' (сноска 7 переписана): «нулевая ошибка <-> восстановление на каждой координате» записано одним утверждением — ' + N_ZR });
  fix('Если система полна на данном усечении $N$, ошибка зануляется', 'parseval_std_all', { theorem: 'fourier_truncation_ends_exactly', file: PO,
    claim: 'Если система полна на данном усечении $N$, ошибка зануляется при достаточно большом $K$; для всякого набора из $N$ ортонормированных векторов (в частности, стандартного) — точно при $K=N$: процесс усечения завершается *точным* восстановлением за конечное число шагов.',
    note: DONE + ': было «для стандартного полного N-направленного набора»; доказано для всякого набора из N ортонормированных векторов. ' + N_END });
  // --- сноска 1
  fix('Опорные файлы — `ProcessFourierSeriesL2.v` (6 утверждений', null, { file: PO, page_price: '0 аксиом', assumptions: 'все 31 объявление файла: ' + CL,
    claim: 'Опорный файл — `ProcessOrthonormalFourier.v` (каталог `src/process/`, 30 утверждений, 0 `Admitted`, 0 аксиом), поверх `ProcessL2Orthonormal.v` (Часть VI):',
    note: DONE + ': в ProcessOrthonormalFourier.v 30 строк Qed; Admitted, Axiom, Parameter нет; все объявления — ' + CL + '.' }, FS);
  fix('Опорные файлы — `ProcessFourierSeriesL2.v` (6 утверждений', null, { theorem: 'on_all_indices_unsat', file: LO, page_price: '', assumptions: CL,
    claim: 'В прежних `ProcessFourierSeriesL2.v` и `ProcessBestApproximation.v` те же утверждения записаны под условием ортонормированности при всех номерах, на $N$ координатах невыполнимым (`on_all_indices_unsat`).',
    note: DONE + ': ' + N_UNSAT + ' Посылка Hon раздела ON — ProcessFourierSeriesL2.v:47, ProcessBestApproximation.v:70.' }, BA);
  add({ theorem: 'on_count_le_dim', file: PO, claim: L('условие ортонормированности наложено на первые $K_0$ векторов, теоремы доказаны для $K§le K_0$, и $K_0§le N$ (`on_count_le_dim`).'), note: PREM + ' ' + N_CNT });
  fix('поверх L<sup>2</sup>-аппарата Части VI', null, { claim: 'Процессное чтение предела — `ProcessL2RieszFischer.v`.' });
  // --- сноска 3
  fix('`fourier_error_eq` в `ProcessFourierSeriesL2.v`:', 'fourier_error_eq', { theorem: 'fourier_error_eq_b', file: PO,
    claim: L('`fourier_error_eq_b` в `ProcessOrthonormalFourier.v`: $§norm{f-P_K}^2=§norm{f}^2-§texttt{captured}(c,K)$ при $K§le K_0$, где `captured`$(c,K)=§sum_{k<K}c_k^2$.'),
    note: DONE + ': ' + N_ERR });
  fix('Прямое следствие `resid_norm` (Часть VI)', 'resid_norm', { theorem: 'resid_norm_b', file: LO, page_price: '',
    claim: 'Прямое следствие `resid_norm_b` (Часть VI).', note: DONE + ': доказательство fourier_error_eq_b — rewrite (resid_norm_b e N K0 Hon f K HK). ' + N_RESN });
  add({ theorem: 'fourier_error_is_tail_b', file: PO, page_price: '0 аксиом',
    claim: L('Если $K_0$ векторов полны для $f$, эта разность есть сумма квадратов отброшенных коэффициентов $§sum_{K§le k<K_0}c_k^2$ — `fourier_error_is_tail_b`. 0 аксиом.'), note: N_TAIL });
  // --- сноска 4
  fix('`fourier_error_nonneg`; эквивалентно `bessel_general` (Глава 7.1).', 'fourier_error_nonneg', { theorem: 'ferr_nonneg', file: PO,
    claim: '`ferr_nonneg` — неотрицательность ошибки; она верна для любого семейства $e$ (сумма квадратов).', note: DONE + ': ' + N_NN });
  fix('`fourier_error_nonneg`; эквивалентно `bessel_general` (Глава 7.1).', 'bessel_general', { theorem: 'bessel_from_error_b', file: PO, page_price: '0 аксиом',
    claim: 'Неравенство Бесселя следует из неё вместе с тождеством ошибки — `bessel_from_error_b` (то же, что `bessel_b`, Глава 7.1). Обе — в `ProcessOrthonormalFourier.v`, 0 аксиом.',
    note: DONE + ': было «эквивалентно bessel_general» — неотрицательность ошибки верна для любого семейства, неравенство Бесселя — нет; связывает их тождество ошибки. ' + N_BFE });
  // --- сноска 5
  const C5 = L("`fourier_error_monotone_b` ($K§le K'§le K_0$); опирается на монотонность захваченной энергии (`captured_mono`, Глава 7.5).");
  fix('`fourier_error_monotone`; опирается на монотонность захваченной энергии', 'fourier_error_monotone', { theorem: 'fourier_error_monotone_b', file: PO, page_price: '', claim: C5, note: DONE + ': ' + N_MONO });
  fix('`fourier_error_monotone`; опирается на монотонность захваченной энергии', 'captured_mono', { page_price: '', claim: C5 });
  add({ theorem: 'fourier_error_step_b', file: PO, claim: L('Точнее: очередной коэффициент уменьшает ошибку ровно на свой квадрат, $§norm{f-P_{K+1}}^2=§norm{f-P_K}^2-c_K^2$, — `fourier_error_step_b`.'), note: N_STEP });
  add({ theorem: 'monotone_fails_without_on', file: PO, page_price: '0 аксиом', claim: 'Без ортонормированности ошибка может расти — `monotone_fails_without_on`. Все — в `ProcessOrthonormalFourier.v`, 0 аксиом.', note: N_FAIL });
  // --- сноска 6
  const C6 = L('`fourier_partial_best_b` в `ProcessOrthonormalFourier.v` (она же `best_approx_b` из `ProcessL2Orthonormal.v`): $§norm{f-P_K}^2§le§norm{f-§sum_{k<K}a_k e_k}^2$ для любых весов $a_k$, $K§le K_0$;');
  fix('`fourier_partial_best` в `ProcessFourierSeriesL2.v` (она же `best_approx_ge`', 'fourier_partial_best', { theorem: 'fourier_partial_best_b', file: PO, claim: C6, note: DONE + ': ' + N_PB });
  fix('`fourier_partial_best` в `ProcessFourierSeriesL2.v` (она же `best_approx_ge`', 'best_approx_ge', { theorem: 'best_approx_b', file: LO, claim: C6, note: DONE + ': ' + N_BGE });
  fix('единственность минимума — `best_approx_unique`. 0 аксиом.', 'best_approx_unique', { theorem: 'best_approx_unique_b', file: PO,
    claim: 'единственность минимума — `best_approx_unique_b`. 0 аксиом.', note: DONE + ': ' + N_BUN });
  // --- сноска 7
  fix('`fourier_error_zero_iff`: $', 'fourier_error_zero_iff', { theorem: 'fourier_error_zero_iff_b', file: PO, page_price: '',
    claim: L('`fourier_error_zero_iff_b`: $§norm{f-P_K}^2=0 §Leftrightarrow §sum_{k<K}c_k^2=§norm{f}^2$ — из тождества ошибки;'), note: DONE + ': ' + N_ZI });
  fix('опирается на критерий полноты `parseval_iff_complete` (Глава 7.1). 0 аксиом.', 'parseval_iff_complete', { theorem: 'fourier_error_zero_iff_recovers_b', file: PO, page_price: '',
    claim: L('«нулевая ошибка $§Leftrightarrow$ $P_K(m)=f(m)$ при всех $m<N$» — `fourier_error_zero_iff_recovers_b`, через критерий полноты `parseval_iff_complete_b` (Глава 7.1).'),
    note: DONE + ': было «fourier_error_zero_iff опирается на parseval_iff_complete» — её доказательство критерием полноты не пользовалось. Теперь связь записана отдельной теоремой. ' + N_ZR });
  add({ theorem: 'fourier_truncation_ends_exactly', file: PO, page_price: '0 аксиом',
    claim: 'Точное восстановление при $K=N$ для $N$ ортонормированных векторов — `fourier_truncation_ends_exactly` (через `full_on_recovers`); для стандартного базиса — `std_truncation_ends_exactly`, для повёрнутого — `rot_truncation_ends_exactly`. Все — в `ProcessOrthonormalFourier.v`, 0 аксиом.', note: N_END });
  for (const th of ['full_on_recovers', 'std_truncation_ends_exactly', 'rot_truncation_ends_exactly']) add({ theorem: th, file: PO, page_price: '0 аксиом',
    claim: 'Точное восстановление при $K=N$ для $N$ ортонормированных векторов — `fourier_truncation_ends_exactly` (через `full_on_recovers`); для стандартного базиса — `std_truncation_ends_exactly`, для повёрнутого — `rot_truncation_ends_exactly`. Все — в `ProcessOrthonormalFourier.v`, 0 аксиом.', note: th === 'full_on_recovers' ? N_FULL : N_END });
  // --- сноска 8
  add({ theorem: null, file: PO, claim: L('`ProcessOrthonormalFourier.v` — Roles: `ferr` — квадрат ошибки как функция стадии $K$; P4: $K§le K_0§le N$, процесс усечений заканчивается точным восстановлением при $K=N$.'),
    note: 'Шапка файла: Roles — [ferr e f N K] — the squared error ||f - P_K||^2 of the K-term partial sum: a function of the stage K of the truncation process; P4 diagnostic — K ranges over the vectors actually given (K <= K0 <= N); the truncation process … ends with exact recovery at K = N.' });
  save();
}

// ================= Глава VII.5 (место 5.4; слова не менялись) =================
{
  const { fix, save } = open('part07-ch05');
  fix('Глава 7.4 дала конечное ядро контроля усечений: ошибка усечения равна отброшенной хвостовой энергии, не возрастает', null, { theorem: 'fourier_error_eq_b', file: PO, assumptions: CL,
    note: BYF + ': ' + N_ERR + ' ' + N_MONO + ' ' + N_ZI });
  fix('*Глава 7.1* переформулировала L<sup>2</sup>-аппарат Части VI как теорию коэффициентов Фурье', null, { theorem: 'bessel_b', file: LO, assumptions: CL,
    note: BYF + ': ' + N_BESSEL + ' Парсеваль — parseval_iff_complete_b (:296); наилучшее приближение — best_approx_b (:256), best_approx_unique_b (ProcessOrthonormalFourier.v:178).' });
  fix('*Глава 7.4* дала конечное ядро контроля усечений: ошибка усечения равна хвостовой энергии и монотонно не возрастает.', null, { theorem: 'fourier_error_monotone_b', file: PO, assumptions: CL,
    note: BYF + ': ' + N_MONO + ' ' + N_TAIL });
  fix('неравенство Бесселя и критерий Парсеваля, наилучшее приближение, конечное ядро контроля усечений,', null, { theorem: 'parseval_iff_complete_b', file: LO, assumptions: CL,
    note: BYF + ': ' + N_PIC + ' Бессель — bessel_b (:243); наилучшее приближение — best_approx_b (:256); ядро усечений — ProcessOrthonormalFourier.v (fourier_error_eq_b :294, fourier_error_monotone_b :326, fourier_truncation_ends_exactly :500).' });
  save();
}

// ================= поле assumptions у записей, получивших теорему (повторяемо) =================
for (const [name, list] of [
  ['part07-ch04', [['Доказано над ℚ следующее (для конечной ортонормированной системы', 'fourier_error_eq_b'],
                   ['*Первый* — конечная теория усечений', 'fourier_truncation_ends_exactly'],
                   ['В прежних `ProcessFourierSeriesL2.v` и `ProcessBestApproximation.v`', 'on_all_indices_unsat']]],
  ['part07-ch05', [['Глава 7.4 дала конечное ядро контроля усечений: ошибка усечения равна отброшенной хвостовой энергии, не возрастает', 'fourier_error_eq_b'],
                   ['*Глава 7.1* переформулировала L<sup>2</sup>-аппарат Части VI как теорию коэффициентов Фурье', 'bessel_b'],
                   ['*Глава 7.4* дала конечное ядро контроля усечений: ошибка усечения равна хвостовой энергии и монотонно не возрастает.', 'fourier_error_monotone_b'],
                   ['неравенство Бесселя и критерий Парсеваля, наилучшее приближение, конечное ядро контроля усечений,', 'parseval_iff_complete_b']]],
]) {
  const { fix, save } = open(name);
  for (const [prefix, th] of list) fix(prefix, th, { assumptions: CL });
  save();
}
