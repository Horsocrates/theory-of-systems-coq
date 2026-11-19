// Часть VII, шаг 3, страницы (2026-11-18, слово автора «Делай»): 9 правок главы VII.2 внесены
// (вентиль Адамара над Q[sqrt 2]: «что доказано», раздел о вентиле, суперпозиция, итоговый курсив,
//  «над Q» в разборе E/R/R; сноски 1, 7, 8, 9).
// Формализация — новый src/process/ProcessHadamardGateSqrt2.v; прежние файлы не менялись.
// Запуск: node patch-p07-step-03-pages.cjs  (затем relocate + merge по part07-ch02). Скрипт повторяем.
// Внимание: строки с настоящим знаком параграфа через L() не пропускать.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 18.11 (Часть VII, шаг 3, слово автора)';
const BYF = DONE + ' (формализацией; текст страницы не менялся)';
const CL = 'Closed under the global context';
const HG2 = 'src/process/ProcessHadamardGateSqrt2.v';
const HG = 'src/process/ProcessHadamardGate.v';
const BS = String.fromCharCode(92);
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

// --- утверждения нового файла (номера строк — src/process/ProcessHadamardGateSqrt2.v)
const N_UNS = 'hgate_premise_unsat : forall s : Q, ~ (s * s * 2 == 1) (:66) — посылка раздела Gate файла ProcessHadamardGate.v (:68–69) невыполнима; через Sqrt2Irrational.no_rational_sqrt2. ' + CL + '.';
const N_SQ = 'hgate_sq_scale : forall (s : Q) f m, m < pow2 1 -> hgate s (hgate s f) m == (s * s * 2) * f m (:75) — без посылки. ' + CL + '.';
const N_NEV = 'hgate_never_involution_over_Q : forall s : Q, ~ (forall f m, m < pow2 1 -> hgate s (hgate s f) m == f m) (:101); через hgate_involution_iff (:86): вентиль с рациональным множителем — инволюция <-> s * s * 2 == 1. ' + CL + '.';
const N_REL = 's2_relation_holds : req (rmul (rmul s2 s2) (2, 0)) r1 (:148), где s2 := (0, 1 # 2) — пара 0 + (1/2)·√2 = 1/√2 в ℚ[√2] (CliffordField.v:110); s2_sq_half : req (rmul s2 s2) (1 # 2, 0) (:155). ' + CL + '.';
const N_INV = 'hgateR_involution : forall (f : nat -> RQ) m, m < pow2 1 -> req (hgateR (hgateR f) m) (f m) (:181) — без посылок; hgateR f m := rmul s2 (Σ_{j<2} had 1 m j · f j) (:143), амплитуды — пары рациональных (CliffordField.RQ). ' + CL + '.';
const N_SUP = 'hgateR_superposition : req (hgateR e0R 0) s2 ' + AND + ' req (hgateR e0R 1) s2 (:198); e0R — состояние |0⟩ (:194). ' + CL + '.';
const N_ISO = 'hgateR_isometry : forall f : nat -> RQ, req (radd (rmul (hgateR f 0) (hgateR f 0)) (rmul (hgateR f 1) (hgateR f 1))) (radd (rmul (f 0) (f 0)) (rmul (f 1) (f 1))) (:210). ' + CL + '.';
const N_ROWS = 'hgateR_rows (:165): req (hgateR f 0) (radd (rmul s2 (f 0)) (rmul s2 (f 1))) ' + AND + ' req (hgateR f 1) (radd (rmul s2 (f 0)) (rmul ns2 (f 1))) — строки матрицы mH = (s2, s2, s2, ns2) файла CliffordField.v (:112); mH_invol : rm_eq (rm_mul mH mH) rm_id (CliffordField.v:129). ' + CL + '.';
const N_HALF = 'half_HH_is_identity : forall f m, m < pow2 1 -> (1 # 2) * op_apply (had 1) (op_apply (had 1) f (pow2 1)) (pow2 1) m == f m (:123). ' + CL + '.';
const N_WINV = 'walsh_inverse : forall k f m, m < pow2 k -> op_apply (had k) (fun j => / inject_Z (Z.of_nat (pow2 k)) * op_apply (had k) f (pow2 k) j) (pow2 k) m == f m (:112); из walsh_HH (ProcessFourierON.v:61). ' + CL + '.';

{
  const { fix, add, save } = open('part07-ch02');
  // --- правка 1: «что доказано»
  const C37 = L('Наконец, нормированный случай $N=2$ — это в точности квантовый вентиль Адамара: множитель $s=1/§sqrt2$ с соотношением $s^2§cdot2=1$ не рационален, и вентиль построен над расширенным носителем ℚ[√2] — парами рациональных чисел $a+b§sqrt2$.');
  fix('Наконец, нормированный случай $N=2$, если вынести', 'hgate_involution', { theorem: 'hgateR_involution', file: HG2, claim: C37,
    note: DONE + ': было «если вынести 1/√2 в абстрактный параметр s с соотношением s²·2 = 1» — параметр раздела Gate рационален, и соотношение невыполнимо. Теперь вентиль построен над ℚ[√2]. ' + N_INV + ' ' + N_REL });
  add({ theorem: 'hgate_premise_unsat', file: HG2, claim: C37, note: N_UNS });
  // --- правка 2: раздел о вентиле
  fix('Две его определяющие черты доказаны как', 'hgate_involution', { theorem: 'hgateR_involution', file: HG2,
    claim: L('Две его определяющие черты доказаны точно — над носителем ℚ[√2], где единственная иррациональность, $§sqrt2$, есть элемент: пара рациональных чисел.'),
    note: DONE + ': было «доказаны как рациональные факты, с единственной трансцендентностью — нормировкой — вынесенной в абстрактный параметр»: инволюция была доказана только под невыполнимой посылкой; √2 алгебраичен. ' + N_INV + ' ' + N_SUP });
  const C224 = 'Над самим ℚ такого вентиля нет: при рациональном множителе $s$ дважды применённый вентиль есть умножение на $2s^2$, а $2s^2=1$ в ℚ неразрешимо.';
  add({ theorem: 'hgate_sq_scale', file: HG2, claim: C224, note: N_SQ });
  add({ theorem: 'hgate_never_involution_over_Q', file: HG2, claim: C224, note: N_NEV + ' ' + N_UNS });
  // --- инволюция и суперпозиция (правка 3)
  fix('Во-первых, вентиль есть *инволюция*', 'hgate_involution', { theorem: 'hgateR_involution', file: HG2, note: BYF + ' (сноска 8 переписана): ' + N_INV });
  const C227 = L('Во-вторых, он создаёт *равную суперпозицию*: из базисного состояния $§lvert0§rangle$ он делает вектор с равными амплитудами $1/§sqrt2$ на обоих исходах; квадрат амплитуды рационален: $1/2$.[^9]');
  fix('Во-вторых, он создаёт *равную суперпозицию*', 'hgate_superposition', { theorem: 'hgateR_superposition', file: HG2, claim: C227,
    note: DONE + ' (добавлено о квадрате амплитуды): ' + N_SUP });
  add({ theorem: 's2_sq_half', file: HG2, claim: C227, note: N_REL });
  // --- правка 4: итоговый курсив
  fix('Единственная иррациональность — нормировка', 'hgate_involution', { theorem: 'hgateR_involution', file: HG2,
    claim: L('Единственная иррациональность — нормировка $1/§sqrt N$ — отделена и помечена; структура вентиля (инволюция, суперпозиция) доказана над ℚ[√2], а в ℚ остаются $H(Hf)=2f$ и квадрат амплитуды $1/2$.'),
    note: DONE + ': было «структура вентиля (инволюция, суперпозиция) рациональна» — при рациональном множителе вентиль не инволюция (hgate_never_involution_over_Q, :101). ' + N_INV + ' В ℚ: hadamard_unnormalised_square (ProcessHadamardGate.v:59) — H(Hf) = 2f; s2_sq_half (:155) — квадрат амплитуды 1/2.' });
  // --- сноска 1
  const C1 = 'дополненный `ProcessFourierON.v` (5 утверждений), `ProcessWalshCharacter.v` (8 утверждений), `ProcessHadamardGate.v` (5 утверждений), `ProcessOrthogonalWalsh.v` (32 утверждения) и `ProcessHadamardGateSqrt2.v` (14 утверждений).';
  const P1 = 'дополненный `ProcessFourierON.v` (5 утверждений), `ProcessWalshCharacter.v` (8 утверждений), `ProcessHadamardGate.v` (5 утверждений) и `ProcessOrthogonalWalsh.v`';
  for (const f of ['src/process/ProcessFourierON.v', 'src/process/ProcessWalshCharacter.v', HG, 'src/process/ProcessOrthogonalWalsh.v']) fix(P1, null, { claim: C1 }, f);
  add({ theorem: null, file: HG2, assumptions: 'все 18 объявлений файла: ' + CL, claim: C1, note: 'В ProcessHadamardGateSqrt2.v 14 строк Qed и четыре определения; Admitted, Axiom, Parameter нет; все объявления — ' + CL + '.' });
  // --- сноска 7
  add({ theorem: 'walsh_inverse', file: HG2, claim: L('В виде обратного преобразования, $H§big(§tfrac1N Hf§big)=f$ при всяком $N=2^k$, — `walsh_inverse` (`ProcessHadamardGateSqrt2.v`).'), note: N_WINV });
  // --- сноска 8
  const C8a = L('`hgateR_involution` в `ProcessHadamardGateSqrt2.v`: над ℚ[√2] — парами $a+b§sqrt2$ из `CliffordField.v`, где $s=1/§sqrt2$ есть пара $(0,1/2)$ и соотношение $s^2§cdot2=1$ выполнено (`s2_relation_holds`), — дважды применённый вентиль возвращает состояние; посылок теорема не берёт.');
  fix('`hgate_involution` в `ProcessHadamardGate.v`: для нормированного вентиля', 'hgate_involution', { theorem: 'hgateR_involution', file: HG2, claim: C8a, note: DONE + ': ' + N_INV });
  add({ theorem: 's2_relation_holds', file: HG2, claim: C8a, note: N_REL });
  const C8b = L('В `ProcessHadamardGate.v` параметр $s$ рационален, а рационального $s$ с $s^2§cdot2=1$ нет (`hgate_premise_unsat`): при рациональном множителе дважды применённый вентиль есть умножение на $2s^2$ (`hgate_sq_scale`) и тождественным не бывает (`hgate_never_involution_over_Q`).');
  add({ theorem: 'hgate_premise_unsat', file: HG2, claim: C8b, note: N_UNS });
  add({ theorem: 'hgate_sq_scale', file: HG2, claim: C8b, note: N_SQ });
  add({ theorem: 'hgate_never_involution_over_Q', file: HG2, claim: C8b, note: N_NEV });
  fix('тождество $H(Hf)=2f$ (частный случай $N=2$) тогда даёт', 'hadamard_unnormalised_square', { theorem: 'half_HH_is_identity', file: HG2,
    claim: L('Рациональная форма обратимости — $§tfrac12 H(Hf)=f$ (`half_HH_is_identity`).'),
    note: DONE + ': прежняя фраза («тождество H(Hf) = 2f тогда даёт s²·2·f = f») снята вместе с параметром s. ' + N_HALF + ' Из hadamard_unnormalised_square (ProcessHadamardGate.v:59).' });
  const C8c = 'Тот же вентиль в матричной записи — `mH_invol` (`CliffordField.v`), связь — `hgateR_rows`.';
  add({ theorem: 'mH_invol', file: 'src/stdlib/CliffordField.v', claim: C8c, note: 'mH_invol : rm_eq (rm_mul mH mH) rm_id (CliffordField.v:129), mH := (s2, s2, s2, ns2) (:112) — матрица (1/√2)[[1,1],[1,−1]] над ℚ[√2]. ' + CL + '.' });
  add({ theorem: 'hgateR_rows', file: HG2, page_price: '0 аксиом', claim: C8c, note: N_ROWS });
  // --- сноска 9
  const C9a = '`hgateR_superposition`: над ℚ[√2] вентиль переводит $e_0$ в $(s,s)$ — равные амплитуды на двух координатах; квадрат амплитуды — рациональное $1/2$ (`s2_sq_half`); сумма квадратов амплитуд сохраняется для любого состояния (`hgateR_isometry`).';
  add({ theorem: 'hgateR_superposition', file: HG2, claim: C9a, note: N_SUP });
  add({ theorem: 's2_sq_half', file: HG2, claim: C9a, note: N_REL });
  add({ theorem: 'hgateR_isometry', file: HG2, claim: C9a, note: N_ISO });
  fix('`hgate_superposition`: $' + BS + 'texttt{hgate} e_0', 'hgate_superposition', {
    claim: 'В `ProcessHadamardGate.v` равенство `hgate_superposition` верно для любого рационального множителя и нормировки не использует.',
    note: DONE + ': hgate_superposition (ProcessHadamardGate.v:93): hgate s2inv e0 0 == s2inv ' + AND + ' hgate s2inv e0 1 == s2inv; доказательство посылкой Hs2 не пользуется, после закрытия раздела — forall s2inv : Q. ' + CL + '.' });
  save();
}
