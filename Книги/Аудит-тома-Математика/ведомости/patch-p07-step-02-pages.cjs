// Часть VII, шаг 2, страницы (2026-11-18, слово автора «Делай»): 10 правок глав VII.1 (5) и VII.2 (5) внесены
// (нормировка Уолша: чётные и нечётные k; теория Главы 7.1 в ортогональной форме; анонс главы VII.2;
//  число в сноске 1 главы VII.2; новые сноски 17 (VII.1) и 11 (VII.2)).
// Формализация — новый src/process/ProcessOrthogonalWalsh.v; прежние файлы не менялись.
// Запуск: node patch-p07-step-02-pages.cjs  (затем relocate + merge по part07-ch01, ch02). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 18.11 (Часть VII, шаг 2, слово автора)';
const BYF = DONE + ' (формализацией; текст страницы не менялся)';
const CL = 'Closed under the global context';
const OW = 'src/process/ProcessOrthogonalWalsh.v';
const BS = String.fromCharCode(92);
const L = (s) => s.split('§').join(BS);   // «§» — обратная косая черта
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

// --- утверждения нового файла (номера строк — src/process/ProcessOrthogonalWalsh.v)
const P_OG = 'Посылки раздела: forall k, k < K0 -> 0 < d k; forall i j, i < K0 -> j < K0 -> seq_inner (e i) (e j) N == (if Nat.eqb i j then d i else 0); og_coef k := seq_inner (e k) f N / d k (:160).';
const N_RN = 'resid_norm_og : K <= K0 -> ‖f − Σ_{k<K} og_coef k · e_k‖² == seq_inner f f N - q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N / d k) K (:176). ' + P_OG + ' ' + CL + '.';
const N_RO = 'resid_ortho_og : j < K -> K <= K0 -> seq_inner (e j) (fun m => f m - q_sum (fun k => og_coef k * e k m) K) N == 0 (:166); через proj_coord_og (:120). ' + P_OG + ' ' + CL + '.';
const N_BO = 'bessel_og : K <= K0 -> q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N / d k) K <= seq_inner f f N (:191). ' + P_OG + ' ' + CL + '.';
const N_BEQ = 'best_approx_eq_og : K <= K0 -> ‖f − Σ_{k<K} a_k e_k‖² == ‖f − P_K‖² + q_sum (fun k => d k * ((a k - og_coef k) * (a k - og_coef k))) K (:203); best_approx_og (:217): ‖f − P_K‖² <= ‖f − Σ_{k<K} a_k e_k‖². ' + P_OG + ' ' + CL + '.';
const N_BUN = 'best_approx_unique_og : K <= K0 -> (‖f − Σ_{k<K} a_k e_k‖² == ‖f − P_K‖²) <-> (forall k, k < K -> a k == og_coef k) (:233). ' + P_OG + ' ' + CL + '.';
const N_PIC = 'parseval_iff_complete_og : K <= K0 -> (q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N / d k) K == seq_inner f f N) <-> (forall m, m < N -> q_sum (fun k => og_coef k * e k m) K == f m) (:263). ' + P_OG + ' ' + CL + '.';
const N_WOG = 'walsh_og : i < pow2 k -> j < pow2 k -> seq_inner (had k i) (had k j) (pow2 k) == (if Nat.eqb i j then inject_Z (Z.of_nat (pow2 k)) else 0) (:298) — посылка раздела OrthogonalSystem с d = N, K0 = N. ' + CL + '.';
const N_WB = 'walsh_bessel : K <= pow2 k -> q_sum (fun i => seq_inner (had k i) f (pow2 k) * seq_inner (had k i) f (pow2 k) / inject_Z (Z.of_nat (pow2 k))) K <= seq_inner f f (pow2 k) (:309); из bessel_og (:191) и walsh_og (:298). ' + CL + '.';
const N_WBA = 'walsh_best_approx : K <= pow2 k -> ‖f − Σ_{i<K} (⟨H_i,f⟩/N) H_i‖² <= ‖f − Σ_{i<K} a_i H_i‖² для любых весов a (:321); из best_approx_og (:217). ' + CL + '.';
const N_WPD = 'walsh_parseval_divided : forall k f, q_sum (fun i => seq_inner (had k i) f (pow2 k) * seq_inner (had k i) f (pow2 k) / inject_Z (Z.of_nat (pow2 k))) (pow2 k) == seq_inner f f (pow2 k) (:336); из parseval_walsh (ProcessFourierON.v:91). ' + CL + '.';
const N_WC = 'walsh_complete : m < pow2 k -> q_sum (fun i => seq_inner (had k i) f (pow2 k) / inject_Z (Z.of_nat (pow2 k)) * had k i m) (pow2 k) == f m (:353); из parseval_iff_complete_og (:263) и walsh_parseval_divided (:336). ' + CL + '.';
const N_WCT = 'walsh_coef_is_transform : seq_inner (had k i) f (pow2 k) = op_apply (had k) f (pow2 k) i (:304) — по определению. ' + CL + '.';
const N_WRD = "walsh_rows_distinct : i < pow2 k -> i' < pow2 k -> i <> i' -> ~ (forall j, j < pow2 k -> had k i j == had k i' j) (:366); из hadamard_orthogonal и walsh_norm. " + CL + '.';
const N_EVEN = 'walsh_rational_norm_iff_even : forall k, (exists s : Q, s * s == inject_Z (Z.of_nat (pow2 k))) <-> Nat.Even k (:512); из walsh_even_norm_exists (:464) и walsh_odd_no_rational_norm (:492). ' + CL + '.';
const N_4J = "walsh_4j_orthonormal : i < pow2 (2 * j) -> i' < pow2 (2 * j) -> seq_inner (walsh_n (2 * j) s i) (walsh_n (2 * j) s i') (pow2 (2 * j)) == (if Nat.eqb i i' then 1 else 0) при s = inject_Z (Z.of_nat (pow2 j)) (:472); walsh_n k s i m := had k i m / s (:385); пример N = 4, s = 2 — walsh_4_orthonormal (:484). " + CL + '.';
const N_ODD = 'walsh_odd_no_rational_norm : forall j s, ~ (s * s == inject_Z (Z.of_nat (pow2 (S (2 * j))))) (:492); через Sqrt2Irrational.no_rational_sqrt2; для N = 2 — walsh_2_no_rational_norm (:508). ' + CL + '.';
const N_WNO = 'walsh_normalized_on : s * s == inject_Z (Z.of_nat (pow2 k)) -> forall i j, i < pow2 k -> j < pow2 k -> seq_inner (walsh_n k s i) (walsh_n k s j) (pow2 k) == (if Nat.eqb i j then 1 else 0) (:390) — посылка Hon раздела ONB (ProcessL2Orthonormal.v) с K0 = N; walsh_normalized_bessel (:408), walsh_normalized_parseval (:420), walsh_normalized_complete (:444). Рациональное s есть в точности при чётном k (:512). ' + CL + '.';

// ================= Глава VII.1 =================
{
  const { fix, add, save } = open('part07-ch01');
  // знак параграфа в цитате — настоящий, поэтому вынесен из L()
  const C43 = L('Чего глава *не* делает: она не строит завершённый *бесконечный* ортонормированный базис, не утверждает, что замкнутая оболочка системы есть всё пространство, и не извлекает корень $§sqrt N$: нормировка $1/§sqrt N$ рациональна лишь когда $N$ — точный квадрат, а в остальных случаях теория ведётся для ортогональной системы без нормировки (') + String.fromCharCode(167) + ' «Конкретная ортогональная система: Уолш–Адамар»).';
  fix('Чего глава *не* делает: она не строит завершённый *бесконечный* ортонормированный базис, не утверждает, что замкнутая оболочка системы есть всё пространство, и не извлекает корень', 'walsh_rational_norm_iff_even', { claim: C43 });
  fix('Чего глава *не* делает: она не строит завершённый *бесконечный* ортонормированный базис, не утверждает, что замкнутая оболочка системы есть всё пространство, и не вводит нормировку', null, {
    theorem: 'walsh_rational_norm_iff_even', file: OW, assumptions: CL,
    claim: C43,
    note: DONE + ': было «не вводит нормировку 1/√N иначе как абстрактным параметром» — параметра нормировки в опорных файлах главы нет. Теперь: корень не извлекается, теория ведётся для ортогональной системы. ' + N_EVEN + ' ' + N_BO });
  fix('Чтобы получить из них ортонормированную систему в смысле `Hon`', 'on_all_indices_unsat', { theorem: 'walsh_normalized_on', file: OW,
    note: BYF + ' (следующая фраза переписана): ' + N_WNO });
  fix('И вот здесь — единственная иррациональность: множитель $1/' + BS + 'sqrt N$ рационален лишь когда $N$ — точный квадрат (например', null, {
    theorem: 'walsh_4j_orthonormal', file: OW, assumptions: CL,
    claim: L('И вот здесь — единственная иррациональность: множитель $1/§sqrt N$ рационален лишь когда $N$ — точный квадрат, то есть при чётном $k$ ($N=4^j$, $§sqrt N=2^j$; например $N=4$, $§sqrt N=2$): тогда нормированные строки удовлетворяют `Hon`, и это доказано.'),
    note: DONE + ': было «в общем случае вводится абстрактным параметром s с условием s² = N» — такого параметра в формализации нет, а рационального s при нечётном k не существует. ' + N_4J + ' ' + N_EVEN });
  const C295 = L('При нечётном $k$ рационального $s$ с $s^2=N$ нет — это тоже доказано,— и корень не вводится вовсе: вся теория главы пересказана для *ортогональной* системы с квадратами норм $d_k$ (коэффициент $c_k=§inner{e_k}{f}/d_k$), так что в наблюдаемых величинах стоит $N$, а не $§sqrt N$,— в согласии с приёмом Части VI (корень в наблюдаемых величинах сокращается).[^17]');
  add({ theorem: 'walsh_odd_no_rational_norm', file: OW, claim: C295, note: N_ODD });
  add({ theorem: 'bessel_og', file: OW, claim: C295, note: N_BO + ' Остальные теоремы раздела — resid_norm_og (:176), best_approx_eq_og (:203), best_approx_unique_og (:233), parseval_iff_complete_og (:263).' });
  fix('Переход к нормированной системе делит обе части на $N$ и возвращает Парсеваль в форме', null, {
    theorem: 'walsh_parseval_divided', file: OW, assumptions: CL,
    claim: L('Деление обеих частей на $N$ возвращает Парсеваль в форме $§sum_k c_k^2 = §norm{f}^2$ с $c_k^2=§inner{H_k}{f}^2/N$ — при всяком $k$ и без корня.'),
    note: DONE + ': было «Переход к нормированной системе делит обе части на N» — нормированная система над ℚ есть только при чётном k; делённая форма равенства верна при всяком k. ' + N_WPD });
  fix('Следующая глава предъявляет конкретную рациональную ортонормированную систему', 'hadamard_orthogonal', {
    claim: L('Следующая глава предъявляет конкретную рациональную ортогональную систему во всей полноте — преобразование Уолша–Адамара. Там абстрактная гипотеза `Hon` сменяется доказанным тождеством $H_N^{§mathsf T}H_N = N§cdot I$, а сохранение энергии — дискретным равенством Планшереля $§norm{Hf}^2 = N§norm{f}^2$: Фурье, построенный без единой трансцендентности.'),
    note: DONE + ': было «ортонормированную систему» — строки Уолша ортогональны с квадратом нормы N. hadamard_orthogonal (ProcessWalshHadamard.v:152): при i, i\' < 2^k сумма произведений строк равна 2^k при i = i\' и 0 иначе. ' + CL + '.' });
  // --- сноска 17
  add({ theorem: null, file: OW, page_price: '0 аксиом', assumptions: 'все 34 объявления файла: ' + CL, claim: 'Файл `ProcessOrthogonalWalsh.v` (32 утверждения, 0 аксиом).',
    note: 'В файле 32 строки Qed и два определения (og_coef, walsh_n); Admitted, Axiom, Parameter нет; все объявления — ' + CL + '.' });
  const S2 = L('Ортогональная система с квадратами норм $d_k>0$, $K§le K_0$: тождество остатка `resid_norm_og`, ортогональность остатка `resid_ortho_og`, Бессель `bessel_og` ($§sum_{k<K}§inner{e_k}{f}^2/d_k§le§norm{f}^2$), наилучшее приближение `best_approx_eq_og` с единственностью `best_approx_unique_og`, критерий полноты `parseval_iff_complete_og`.');
  for (const [th, nt] of [['resid_norm_og', N_RN], ['resid_ortho_og', N_RO], ['bessel_og', N_BO], ['best_approx_eq_og', N_BEQ], ['best_approx_unique_og', N_BUN], ['parseval_iff_complete_og', N_PIC]])
    add({ theorem: th, file: OW, claim: S2, note: nt });
  const S3 = L('Для строк Уолша при всяком $N=2^k$ ($d_k=N$): `walsh_bessel`, `walsh_best_approx`, `walsh_parseval_divided` ($§sum_{i<N}§inner{H_i}{f}^2/N=§norm{f}^2$), `walsh_complete` ($f(m)=§sum_{i<N}(§inner{H_i}{f}/N)§,H_i(m)$).');
  for (const [th, nt] of [['walsh_bessel', N_WB], ['walsh_best_approx', N_WBA], ['walsh_parseval_divided', N_WPD], ['walsh_complete', N_WC]])
    add({ theorem: th, file: OW, claim: S3, note: nt });
  const S4 = 'Нормировка: рациональное $s$ с $s^2=2^k$ существует тогда и только тогда, когда $k$ чётно, — `walsh_rational_norm_iff_even`; при $N=4^j$ строки, делённые на $2^j$, удовлетворяют `Hon` — `walsh_4j_orthonormal`; при нечётном $k$ такого $s$ нет — `walsh_odd_no_rational_norm`.';
  for (const [th, nt] of [['walsh_rational_norm_iff_even', N_EVEN], ['walsh_4j_orthonormal', N_4J], ['walsh_odd_no_rational_norm', N_ODD]])
    add({ theorem: th, file: OW, claim: S4, note: nt });
  save();
}

// ================= Глава VII.2 =================
{
  const { fix, add, save } = open('part07-ch02');
  fix('Буквальная *ортонормированность*', null, { theorem: 'walsh_rational_norm_iff_even', file: OW, assumptions: CL,
    claim: L('Буквальная *ортонормированность* $§inner{e_i}{e_j}=§delta_{ij}$ требует множителя $1/§sqrt N$, рационального лишь когда $N$ — точный квадрат (для $N=2^k$ — в точности при чётном $k$, и это доказано); поэтому при нечётном $k$ над ℚ нормировки нет, и теория ведётся для ортогональной системы с квадратом нормы $N$.'),
    note: DONE + ': было «поэтому нормировка вводится абстрактным параметром, а не вычисляется» — параметра для общего N в формализации нет; что 1/√N рационально лишь при чётном k, теперь теорема. ' + N_EVEN + ' ' + N_4J + ' Параметр вентиля при N = 2 — шаг 3.' });
  fix('Именно это и делает Уолша–Адамара точкой опоры рациональной гармонии', null, { theorem: 'walsh_bessel', file: OW, assumptions: CL,
    claim: L('Именно это и делает Уолша–Адамара точкой опоры рациональной гармонии: ортогональная система, на которой выполняется вся абстрактная теория Главы 7.1 в ортогональной форме — с квадратом нормы $N$ на месте единицы (коэффициенты, проекция, Бессель, Парсеваль),— причём каждая её предпосылка — $§inner{e_i}{e_j}=N§delta_{ij}$ — не постулат, а доказанное равенство.[^11]'),
    note: DONE + ': было «буквально выполняется вся абстрактная теория Главы 7.1» — её теоремы требуют нормы 1 и к строкам Уолша не применялись. Теперь теория доказана в ортогональной форме и применена: ' + N_WB + ' ' + N_WBA + ' ' + N_WC });
  // --- сноска 1
  const C1 = 'дополненный `ProcessFourierON.v` (5 утверждений), `ProcessWalshCharacter.v` (8 утверждений), `ProcessHadamardGate.v` (5 утверждений) и `ProcessOrthogonalWalsh.v` (32 утверждения).';
  const P1 = 'дополненный `ProcessFourierON.v` (5 утверждений), `ProcessWalshCharacter.v` (7 утверждений)';
  fix(P1, null, { claim: C1 }, 'src/process/ProcessFourierON.v');
  fix(P1, null, { claim: C1, note: DONE + ': было «7 утверждений» — в ProcessWalshCharacter.v 8 строк Qed (шесть лемм о битах, had_character и пример had_character_ex); «7» стояло в шапке файла.' }, 'src/process/ProcessWalshCharacter.v');
  fix(P1, null, { claim: C1 }, 'src/process/ProcessHadamardGate.v');
  add({ theorem: null, file: OW, assumptions: 'все 34 объявления файла: ' + CL, claim: C1, note: 'В ProcessOrthogonalWalsh.v 32 строки Qed; Admitted, Axiom, Parameter нет; все объявления — ' + CL + '.' });
  // --- сноска 4
  add({ theorem: 'walsh_rows_distinct', file: OW, page_price: '0 аксиом', claim: L('Разные строки — разные функции на $§{0,§dots,N-1§}$: `walsh_rows_distinct` (`ProcessOrthogonalWalsh.v`, 0 аксиом).'), note: N_WRD });
  // --- сноска 11
  const T1 = L('Теория Главы 7.1 в ортогональной форме (квадраты норм $d_k$ на месте единиц, коэффициент $c_k=§inner{e_k}{f}/d_k$) — файл `ProcessOrthogonalWalsh.v` (32 утверждения, 0 аксиом): `resid_ortho_og`, `resid_norm_og`, `bessel_og`, `best_approx_og`, `best_approx_unique_og`, `parseval_iff_complete_og`.');
  for (const [th, nt] of [['resid_ortho_og', N_RO], ['resid_norm_og', N_RN], ['bessel_og', N_BO], ['best_approx_og', N_BEQ], ['best_approx_unique_og', N_BUN], ['parseval_iff_complete_og', N_PIC]])
    add({ theorem: th, file: OW, page_price: '0 аксиом', claim: T1, note: nt });
  const T2 = L('К строкам Уолша она применена при всяком $N=2^k$ с $d_k=N$ (`walsh_og`): `walsh_bessel` ($§sum_{i<K}(Hf)_i^2/N§le§norm{f}^2$), `walsh_best_approx`, `walsh_parseval_divided`, `walsh_complete` ($f(m)=§sum_{i<N}§frac{(Hf)_i}{N}§,H_{im}$); коэффициент $§inner{H_i}{f}$ есть $i$-я координата преобразования — `walsh_coef_is_transform`.');
  for (const [th, nt] of [['walsh_og', N_WOG], ['walsh_bessel', N_WB], ['walsh_best_approx', N_WBA], ['walsh_parseval_divided', N_WPD], ['walsh_complete', N_WC], ['walsh_coef_is_transform', N_WCT]])
    add({ theorem: th, file: OW, claim: T2, note: nt });
  const T3 = 'Нормировка: рациональное $s$ с $s^2=2^k$ существует тогда и только тогда, когда $k$ чётно (`walsh_rational_norm_iff_even`); при $N=4^j$ строки, делённые на $2^j$, ортонормированы (`walsh_4j_orthonormal`), и к ним применимы теоремы Главы 7.1 в исходной форме (`walsh_normalized_bessel`, `walsh_normalized_parseval`, `walsh_normalized_complete`).';
  for (const [th, nt] of [['walsh_rational_norm_iff_even', N_EVEN], ['walsh_4j_orthonormal', N_4J], ['walsh_normalized_bessel', N_WNO], ['walsh_normalized_parseval', N_WNO], ['walsh_normalized_complete', N_WNO]])
    add({ theorem: th, file: OW, claim: T3, note: nt });
  save();
}
