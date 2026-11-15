// Часть VI, шаг 7, страницы (2026-11-15, слово автора «Делай»): 14 правок главы VI.6 внесены
// (сохранение энергии — три места; спектр диагонального оператора; «обязаны быть неограниченными»; комплексная
//  постоянная; первый шаг линии Нётер; шаг Кэли; ссылка на пример; сноски 1, 5, 7, 8 и новые 12–15).
// Формализация — новый src/process/ProcessOperatorSpectrumEvolution.v; прежние файлы не менялись.
// Запуск: node patch-p06-step-07-pages.cjs  (затем relocate + merge по part06-ch06). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 15.11 (Часть VI, шаг 7, слово автора)';
const BYF = DONE + ' (формализацией; текст страницы не менялся)';
const CL = 'Closed under the global context';
const OS = 'src/process/ProcessOperatorSpectrumEvolution.v';
const LR = 'src/process/ProcessLadderRational.v';
const CSV = 'src/process/ProcessCompactSpectral.v';
const CCV = 'src/process/ProcessCanonicalCommutator.v';
const BS = String.fromCharCode(92);
const L = (s) => s.split('§').join(BS);   // «§» — обратная косая черта
const AND = '/' + BS;
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
  const save = () => {
    // снятие дублей (одна теорема — одна цитата): остаётся первая запись
    const seen = new Set(); const before = j.records.length;
    j.records = j.records.filter((r) => { const k = (r.theorem || '') + '|' + norm(r.claim); if (seen.has(k)) return false; seen.add(k); return true; });
    if (before !== j.records.length) console.log(name + '.json: снято дублей ' + (before - j.records.length));
    fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + '.json: изменено ' + n + ', примечаний ' + noted + ', добавлено ' + added + ', всего ' + j.records.length); };
  return { j, fix, note, add, save };
}

// утверждения нового файла (номера строк — src/process/ProcessOperatorSpectrumEvolution.v)
const N_ENTRY = 'diag_eigen_is_entry : forall (lam v : nat -> Q) (mu : Q) (n : nat), (forall m, diag_op lam v m == mu * v m) -> ~ v n == 0 -> mu == lam n (:93) — собственное значение диагонального оператора есть элемент диагонали; обратно — diag_eigenvalue (ProcessCompactSpectral.v:72): diag_op lam (ket n) m == lam n * ket n m. ' + CL + '.';
const N_FIN = 'diag_nonzero_value_finitely_often : forall lam mu, (lam ~~ const_process 0) -> ~ mu == 0 -> exists N, forall n, N <= n -> ~ lam n == mu (:104); diag_eigenspace_finite : при тех же посылках и diag_op lam v == mu * v — exists N, forall n, N <= n -> v n == 0 (:121). ' + CL + '.';
const N_RANK = 'diag_finite_rank_approx : forall lam, (lam ~~ const_process 0) -> forall eps, 0 < eps -> exists N, forall (f : nat -> Q) (M : nat), seq_inner (diag_op (lam_tail lam N) f) (diag_op (lam_tail lam N) f) M <= (eps * eps) * seq_inner f f M (:139); lam_tail lam N обнуляет диагональ ниже N (:134): хвост оператора мал по норме равномерно по f и по стадии M. ' + CL + '.';
const N_UNF = 'to_zero_unfold : forall lam, (lam ~~ const_process 0) <-> (forall eps, 0 < eps -> exists N, forall n, N <= n -> Qabs (lam n) < eps) (:81) — заключение diag_spectrum_discrete равносильно его посылке. ' + CL + '.';
const N_COMM = 'isometry_commuting_preserves_energy : forall (U H : nat -> nat -> Q) (N : nat), Isometry U N -> (forall w i, i < N -> op_apply H (op_apply U w N) N i == op_apply U (op_apply H w N) N i) -> EnergyPreserving U H N (:352); через isometry_polarization (:334): изометрия сохраняет скалярное произведение. ' + CL + '.';
const N_BOTH = 'commuting_isometric_evolution_conserves_both (:367): при тех же посылках для всех v, n — seq_inner (evolve U N v n) (evolve U N v n) N == seq_inner v v N ' + AND + ' energy H (evolve U N v n) N == energy H v N. ' + CL + '.';
const N_NOT = 'isometry_not_energy_preserving : Isometry (rotation (3 # 5) (4 # 5)) 2 ' + AND + ' ~ EnergyPreserving (rotation (3 # 5) (4 # 5)) (Hdiag 1 0) 2 (:273). ' + CL + '.';
const N_CAY = 'cayley_step_isometry : forall t : Q, Isometry (rotation (cn_c t) (cn_s t)) 2 (:291), где cn_c t := (1 - t * t) / (1 + t * t), cn_s t := (2 * t) / (1 + t * t) (:285, :286); cayley_step_equation (:299): шаг w = U v удовлетворяет w 0 - v 0 == - t * (w 1 + v 1) ' + AND + ' w 1 - v 1 == t * (w 0 + v 0); cayley_half_is_345 (:309). ' + CL + '.';
const N_CAYE = 'cayley_evolution_conserves_both : forall (t e : Q) (v : nat -> Q) (n : nat), для U := rotation (cn_c t) (cn_s t) — норма и энергия при H = Hdiag e e сохраняются на всех шагах (:384). ' + CL + '.';
const N_CCRC = 'no_finite_ccr_complex : forall (A1 A2 B1 B2 : nat -> nat -> Q) (c1 c2 : Q) (N : nat), 1 <= N -> ([A1,B1] − [A2,B2] == c1·1 на координатах < N) -> ([A1,B2] + [A2,B1] == c2·1 на координатах < N) -> c1 == 0 ' + AND + ' c2 == 0 (:213) — A = A1 + iA2, B = B1 + iB2, постоянная c1 + i c2. ' + CL + '.';
const N_ENTR = 'commutator_concrete_entries (:163): для A = E_01, B = E_10 на двух координатах C = AB − BA имеет C 0 0 == 1, C 0 1 == 0, C 1 0 == 0, C 1 1 == −1. ' + CL + '.';
const N_NSC = 'commutator_concrete_not_scalar (:171): forall c : Q, ~ (C 0 0 == mat_scal c mat_id 0 0 ' + AND + ' C 1 1 == mat_scal c mat_id 1 1). ' + CL + '.';
const N_POS = 'position_commutator_entry : forall (x : nat -> Q) (B : nat -> nat -> Q) (N i j : nat), i < N -> j < N -> mat_sub (mat_mul (qhat x) B N) (mat_mul B (qhat x) N) i j == (x i - x j) * B i j (:241); position_commutator_zero_diagonal (:259). ' + CL + '.';
const N_SYM = 'symmetric_without_rational_eigenvector (:401): для T = [[1,1],[1,−1]] — op_symmetric T 2 ' + AND + ' forall (v : nat -> Q) (lam : Q), is_eigenpair T v lam 2 -> v 0 == 0 ' + AND + ' v 1 == 0 (через no_rational_sqrt2: lam * lam == 2 невозможно). ' + CL + '.';
const N_LWU = 'ladder_weights_unbounded : forall al be : nat -> Q, (forall n, al n * be n == inject_Z (Z.of_nat n)) -> forall K : Q, exists n, K < al n * al n ' + BS + '/ K < be n * be n (' + LR + ':303). ' + CL + '.';
const NEWEN = 'сохранение нормы при изометрической эволюции и энергии — при перестановочности шага с гамильтонианом.';

{
  const { fix, note, add, save } = open('part06-ch06');

  // --- правки 1, 2, 9: сохранение энергии (место 6.5)
  const C29 = 'сохранение нормы (вероятности) при изометрической эволюции и энергии — когда шаг ещё и перестановочен с гамильтонианом.';
  fix('сохранение нормы (вероятности) и энергии при изометрической эволюции.', 'evolution_conserves_energy', {
    theorem: 'isometry_commuting_preserves_energy', file: OS, claim: C29,
    note: DONE + ': было «и энергии при изометрической эволюции» — посылка evolution_conserves_energy иная (шаг сохраняет энергию), а из изометричности сохранение энергии не следует. ' + N_COMM + ' ' + N_NOT });
  add({ theorem: 'commuting_isometric_evolution_conserves_both', file: OS, claim: C29, page_price: 'без аксиом', note: N_BOTH });
  fix('отсутствие конечной реализации канонического коммутатора; сохранение нормы и энергии при изометрической эволюции.', 'evolution_conserves_energy', {
    theorem: 'isometry_commuting_preserves_energy', file: OS,
    claim: 'отсутствие конечной реализации канонического коммутатора; ' + NEWEN,
    note: DONE + ': в части об энергии — ' + N_COMM });
  fix(L('каноническое $[a,a^§dagger]=1$ лестницы и отсутствие конечной реализации коммутатора'), 'evolution_conserves_energy', {
    theorem: 'isometry_commuting_preserves_energy', file: OS,
    claim: L('каноническое $[a,a^§dagger]=1$ лестницы и отсутствие конечной реализации коммутатора ($[A,B]=c§mathbf{1}§Rightarrow c=0$); ') + NEWEN,
    note: DONE + ': в части об энергии — ' + N_COMM + ' О лестнице — commutator_canonical_rational (' + LR + ':256).' });

  // --- правка 3: спектр диагонального оператора (место 6.4)
  const C99 = L('Для *диагонального* оператора, диагональ которого $§lambda_n$ стремится к нулю (модель компактного оператора: для всякого порога лишь конечное число $§lambda_n$ его превосходит), спектр *дискретен*: собственные значения — в точности сами числа $§lambda_n$; всякое ненулевое встречается среди них конечное число раз, и его собственные векторы имеют лишь конечное число ненулевых координат; а сам оператор сколь угодно точно приближается операторами конечного ранга.[^5]');
  fix('Для *диагонального* (компактного) оператора спектр *дискретен*: собственные', 'diag_spectrum_discrete', {
    theorem: 'diag_eigen_is_entry', file: OS, claim: C99,
    note: DONE + ': было — «спектр дискретен: собственные значения убывают к нулю», за чем стояла теорема, повторяющая свою посылку. Стремление диагонали к нулю теперь названо условием. ' + N_ENTRY });
  add({ theorem: 'diag_eigenvalue', file: CSV, claim: C99, note: 'diag_eigenvalue (:72): forall lam n m, diag_op lam (ket n) m == lam n * ket n m — всякое lam n есть собственное значение с собственным вектором ket n. ' + CL + '.' });
  add({ theorem: 'diag_nonzero_value_finitely_often', file: OS, claim: C99, note: N_FIN });
  add({ theorem: 'diag_eigenspace_finite', file: OS, claim: C99, note: N_FIN });
  add({ theorem: 'diag_finite_rank_approx', file: OS, claim: C99, note: N_RANK });
  fix('**Доказана *структура* спектра — Рэлей, ортогональность, дискретность диагональной модели, — без аксиом.**', 'diag_spectrum_discrete', {
    theorem: 'diag_eigen_is_entry', file: OS,
    note: BYF + ': «дискретность диагональной модели» — ' + N_ENTRY + ' ' + N_FIN + ' Рэлей и ортогональность — rayleigh_eq (:112) и eigvec_orthogonal (:148) файла ProcessSelfAdjointSpectral.v.' });

  // --- правка 4: ссылка на пример у границы существования
  fix('А *существование* собственного вектора у *произвольного* самосопряжённого оператора', null, {
    theorem: 'symmetric_without_rational_eigenvector', file: OS,
    claim: 'А *существование* собственного вектора у *произвольного* самосопряжённого оператора — достижимость максимума отношения Рэлея — остаётся честной границей: над ℚ собственные значения, как правило, иррациональны (корень дискриминанта)[^15], и существование требует полноты / компактности',
    note: DONE + ' (добавлена ссылка на пример): статус честный — теоремы существования нет. Слова об иррациональности собственных значений подкреплены примером: ' + N_SYM });

  // --- правка 5: «обязаны быть неограниченными» (место 6.9)
  const C140 = L('У него есть чисто алгебраическое следствие, объясняющее, *почему* $§hat q,§hat p$ обязаны быть бесконечномерными; неограниченность — следующий, более сильный классический факт, и от него здесь доказан след: в лестнице осциллятора один из двух весов растёт без границы.[^14]');
  fix(L('У него есть чисто алгебраическое следствие, объясняющее, *почему* $§hat q,§hat p$ обязаны быть неограниченными'), 'no_finite_ccr', { claim: C140,
    note: DONE + ': было «обязаны быть неограниченными (бесконечномерными)» — доказано отсутствие конечномерной реализации. no_finite_ccr (ProcessCanonicalCommutator.v:125): матрицы N×N. Неограниченность (теорема Винтнера — Виландта) не формализована; страница теперь называет её классическим фактом. ' + CL + '.' });
  add({ theorem: 'ladder_weights_unbounded', file: LR, claim: C140, note: N_LWU });

  // --- правка 6: комплексная постоянная (место 6.7)
  const C150 = L('Канонический коммутатор с $c=i§hbar§ne0$ *не реализуем* никакими конечными матрицами. Доказано над ℚ, без аксиом: и для рациональной постоянной, и для комплексной, записанной парой рациональных чисел.[^7]');
  fix(L('Канонический коммутатор с $c=i§hbar§ne0$ *не реализуем* никакими конечными матрицами. Доказано над ℚ, без аксиом.[^7]'), 'no_finite_ccr', {
    theorem: 'no_finite_ccr_complex', file: OS, claim: C150,
    note: DONE + ': было «Доказано над ℚ, без аксиом» при рациональной постоянной c : Q. ' + N_CCRC });
  add({ theorem: 'no_finite_ccr', file: CCV, claim: C150, page_price: 'над ℚ, без аксиом',
    note: 'no_finite_ccr (:125): рациональные матрицы и рациональная постоянная c; при 1 <= N из [A,B] = c·1 на координатах < N следует c == 0. ' + CL + '.' });

  // --- правка 7: первый шаг линии Нётер
  const C7 = L('Первый её шаг доказан: изометрический шаг, перестановочный с $§hat H$, сохраняет энергию — а одной изометричности для этого мало.[^12]');
  add({ theorem: 'isometry_commuting_preserves_energy', file: OS, claim: C7, note: DONE + ' (добавлено): ' + N_COMM });
  add({ theorem: 'isometry_not_energy_preserving', file: OS, claim: C7, note: N_NOT });
  note('В общем виде это зачаток теоремы Нётер: симметрия эволюции (коммутирование с наблюдаемой) влечёт сохранение', null,
    'Статус честный («зачаток», «продолжаемая»). Первый шаг теперь теорема: перестановочность изометрического шага с гамильтонианом влечёт сохранение энергии — isometry_commuting_preserves_energy (' + OS + ':352, шаг 7); страница говорит об этом следующей фразой. Общего утверждения для произвольной наблюдаемой в src нет.');

  // --- правка 8: шаг Кэли (место 6.6)
  const C222 = L('Точный пропагатор $e^{-i§hat H t}$ — роль-предел (непрерывное время, комплексная экспонента); дискретный шаг строится по образующей рационально (шаг Кэли) и остаётся изометрией, а законы сохранения держатся уже на нём.');
  fix(L('Точный пропагатор $e^{-i§hat H t}$ — роль-предел (непрерывное время, комплексная экспонента); процесс'), null, {
    theorem: 'cayley_step_isometry', file: OS, claim: C222,
    note: DONE + ': было «процесс $' + BS + 'psi_n$ его аппроксимирует» — утверждения о приближении в формализации нет. ' + N_CAY });
  add({ theorem: 'cayley_evolution_conserves_both', file: OS, claim: C222, note: N_CAYE });
  add({ theorem: null, file: null, claim: 'Оценка близости такого шага к экспоненте — за границей главы.[^13]',
    note: 'Статус честный: оценки близости шага Кэли к exp(−iĤt) в src нет; шаг построен для одного уровня в вещественных координатах (Re, Im), образующая — tJ, J = [[0,−1],[1,0]].' });

  // --- правка 11: сноска 5
  const C5a = L('Что всякое $§lambda_n$ есть собственное значение — `diag_eigenvalue` в `ProcessCompactSpectral.v`; что других нет — `diag_eigen_is_entry`; конечная кратность ненулевого значения — `diag_nonzero_value_finitely_often` и `diag_eigenspace_finite`; приближение операторами конечного ранга — `diag_finite_rank_approx` (файл `ProcessOperatorSpectrumEvolution.v`, 0 аксиом).');
  const C5b = 'Стремление диагонали к нулю здесь — посылка; `diag_spectrum_discrete` (`ProcessCompactSpectral.v`, 0 аксиом) записывает её в развёрнутом виде.';
  add({ theorem: 'diag_eigenvalue', file: CSV, claim: C5a, page_price: '0 аксиом', note: 'diag_eigenvalue (:72): forall lam n m, diag_op lam (ket n) m == lam n * ket n m. ' + CL + '.' });
  add({ theorem: 'diag_eigen_is_entry', file: OS, claim: C5a, page_price: '0 аксиом', note: DONE + ': было «`diag_spectrum_discrete` в `ProcessCompactSpectral.v` (0 аксиом)». ' + N_ENTRY });
  add({ theorem: 'diag_nonzero_value_finitely_often', file: OS, claim: C5a, page_price: '0 аксиом', note: N_FIN });
  add({ theorem: 'diag_eigenspace_finite', file: OS, claim: C5a, page_price: '0 аксиом', note: N_FIN });
  add({ theorem: 'diag_finite_rank_approx', file: OS, claim: C5a, page_price: '0 аксиом', note: N_RANK });
  add({ theorem: 'diag_spectrum_discrete', file: CSV, claim: C5b, page_price: '0 аксиом',
    note: 'diag_spectrum_discrete (:82): (lam ~~ const_process 0) -> forall eps, 0 < eps -> exists N, forall n, N <= n -> Qabs (lam n) < eps — развёрнутое определение посылки; сноска это говорит. ' + N_UNF });
  add({ theorem: 'to_zero_unfold', file: OS, claim: C5b, note: N_UNF });

  // --- правка 12: сноска 7 (места 6.7, 6.8)
  const C7a = L('`no_finite_ccr` в `ProcessCanonicalCommutator.v` (0 аксиом): из `trace_commutator_zero` ($§mathrm{tr}[A,B]=0$, опирается на `trace_mul_comm`) и $§mathrm{tr}(c§mathbf{1})=cN$; постоянная $c$ здесь рациональна.');
  const C7b = 'Для комплексных матриц и постоянной $c=c_1+ic_2$, записанных парами рациональных частей, — `no_finite_ccr_complex`: $c_1=c_2=0$.';
  const C7c = L('Конкретный свидетель: $[A,B]=§mathrm{diag}(1,-1)$ (`commutator_concrete_entries`), след $0$ (`trace_commutator_concrete`), не кратен $§mathbf{1}$ (`commutator_concrete_not_scalar`).');
  fix('`no_finite_ccr` в `ProcessCanonicalCommutator.v` (0 аксиом): из `trace_commutator_zero`', 'trace_mul_comm', { claim: C7a });
  add({ theorem: 'no_finite_ccr_complex', file: OS, claim: C7b, note: DONE + ' (добавлено): ' + N_CCRC });
  fix(L('Конкретный свидетель: $[A,B]=§mathrm{diag}(1,-1)$, след $0$, не кратен $§mathbf{1}$.'), 'trace_commutator_concrete', { claim: C7c,
    note: DONE + ': было — пример утверждал только нулевой след. Example trace_commutator_concrete (ProcessCanonicalCommutator.v:150): mat_trace (…) 2 == 0. Элементы коммутатора и «не кратен единичной» — отдельные утверждения нового файла. ' + CL + '.' });
  add({ theorem: 'commutator_concrete_entries', file: OS, claim: C7c, note: N_ENTR });
  add({ theorem: 'commutator_concrete_not_scalar', file: OS, claim: C7c, note: N_NSC });
  add({ theorem: null, file: OS, claim: 'Новые теоремы — в `ProcessOperatorSpectrumEvolution.v`, 0 аксиом.', page_price: '0 аксиом',
    note: 'Print Assumptions для всех 29 объявлений файла (24 доказательства и 5 определений) — ' + CL + ' (tos-audit-build/_p06step7/Verify.out).' });

  // --- правка 13: сноска 8
  const C8 = L('В общем виде, для любой решётки и любой матрицы $B$: $[§hat q,B]_{ij}=(x_i-x_j)B_{ij}$, так что диагональ коммутатора нулевая, — `position_commutator_entry`, `position_commutator_zero_diagonal` (`ProcessOperatorSpectrumEvolution.v`, 0 аксиом).');
  add({ theorem: 'position_commutator_entry', file: OS, claim: C8, page_price: '0 аксиом', note: DONE + ' (добавлено): ' + N_POS });
  add({ theorem: 'position_commutator_zero_diagonal', file: OS, claim: C8, page_price: '0 аксиом', note: N_POS });

  // --- правка 14: новые сноски 12–15
  const C12a = '`isometry_commuting_preserves_energy` и `commuting_isometric_evolution_conserves_both` в `ProcessOperatorSpectrumEvolution.v` (0 аксиом); опорный факт — изометрия сохраняет и скалярное произведение (`isometry_polarization`).';
  const C12b = L('Что одной изометричности мало — `isometry_not_energy_preserving`: поворот $3§text{-}4§text{-}5$ меняет энергию при $§hat H=§mathrm{diag}(1,0)$.');
  add({ theorem: 'isometry_commuting_preserves_energy', file: OS, claim: C12a, page_price: '0 аксиом', note: N_COMM });
  add({ theorem: 'commuting_isometric_evolution_conserves_both', file: OS, claim: C12a, page_price: '0 аксиом', note: N_BOTH });
  add({ theorem: 'isometry_polarization', file: OS, claim: C12a, page_price: '0 аксиом',
    note: 'isometry_polarization : forall (U : nat -> nat -> Q) (N : nat), Isometry U N -> forall a b, seq_inner (op_apply U a N) (op_apply U b N) N == seq_inner a b N (:334). ' + CL + '.' });
  add({ theorem: 'isometry_not_energy_preserving', file: OS, claim: C12b, note: N_NOT });
  const C13 = L('`cayley_step_isometry` (шаг Кэли — изометрия при всяком рациональном $t$), `cayley_step_equation` (он решает неявную схему средней точки $w-v=tJ(w+v)$), `cayley_half_is_345` (поворот $3§text{-}4§text{-}5$ есть шаг Кэли при $t=1/2$), `cayley_evolution_conserves_both` — в `ProcessOperatorSpectrumEvolution.v` (0 аксиом).');
  add({ theorem: 'cayley_step_isometry', file: OS, claim: C13, page_price: '0 аксиом', note: N_CAY });
  add({ theorem: 'cayley_step_equation', file: OS, claim: C13, page_price: '0 аксиом', note: N_CAY });
  add({ theorem: 'cayley_half_is_345', file: OS, claim: C13, page_price: '0 аксиом', note: 'cayley_half_is_345 : cn_c (1 # 2) == 3 # 5 ' + AND + ' cn_s (1 # 2) == 4 # 5 (:309). ' + CL + '.' });
  add({ theorem: 'cayley_evolution_conserves_both', file: OS, claim: C13, page_price: '0 аксиом', note: N_CAYE });
  add({ theorem: 'ladder_weights_unbounded', file: LR, page_price: '0 аксиом',
    claim: L('`ladder_weights_unbounded` в `ProcessLadderRational.v` (0 аксиом): во всякой лестнице с $§alpha_n§beta_n=n$ один из весов неограничен.'),
    note: N_LWU });
  add({ theorem: null, file: null,
    claim: L('Общая теорема о неограниченности операторов с $[A,B]=c§mathbf{1}$ (Винтнер — Виландт) требует нормы оператора и здесь не формализована.'),
    note: 'Статус честный: нормы оператора на полных последовательностях в src нет; доказано отсутствие конечномерной реализации (no_finite_ccr, no_finite_ccr_complex) и неограниченность весов лестницы (ladder_weights_unbounded).' });
  add({ theorem: 'symmetric_without_rational_eigenvector', file: OS, page_price: '0 аксиом',
    claim: L('Пример: симметричная матрица $§bigl(§begin{smallmatrix}1&1§§1&-1§end{smallmatrix}§bigr)$ не имеет ни одного рационального собственного вектора — её собственные значения $§pm§sqrt2$ (`symmetric_without_rational_eigenvector`, `ProcessOperatorSpectrumEvolution.v`, 0 аксиом).'),
    note: DONE + ' (добавлено): ' + N_SYM });

  save();
}
