// Часть VII, шаг 6, страницы (2026-11-18, слово автора «Вариант 1, делай»): 8 правок главы VII.5 внесены
// (оговорка о шкале; сноски 1–5; счёт операций быстрого преобразования назван на странице).
// Формализация — новые src/process/ProcessWalshReconstruction.v и src/process/ProcessFastWalshCost.v;
// прежние файлы не менялись.
// Запуск: node patch-p07-step-06-pages.cjs  (затем relocate + merge по part07-ch05). Скрипт повторяем.
// Внимание: строки с настоящим знаком параграфа через L() не пропускать.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 18.11 (Часть VII, шаг 6, слово автора)';
const KEPT = DONE + ' (формализацией; текст страницы не менялся): ';
const CL = 'Closed under the global context';
const WR = 'src/process/ProcessWalshReconstruction.v';
const CO = 'src/process/ProcessFastWalshCost.v';
const FC = 'src/process/ProcessFourierCompression.v';
const WC = 'src/process/ProcessWalshCompaction.v';
const FW = 'src/process/ProcessFastWalsh.v';
const WG = 'src/process/ProcessWalshConvolutionGeneral.v';
const WCH = 'src/process/ProcessWalshCharacter.v';
const OF = 'src/process/ProcessOrthonormalFourier.v';
const OW = 'src/process/ProcessOrthogonalWalsh.v';
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

// --- утверждения (номера строк — src/process/ProcessWalshReconstruction.v, если не сказано иное)
const HF = 'op_apply (had k) f (pow2 k)';
const N_REC = 'Definition walsh_rec (k K : nat) (f : nat -> Q) : nat -> Q := fun m => op_apply (had k) (spec_trunc (' + HF + ') K) (pow2 k) m / Nq k (:114), где spec_trunc c K i = c i при i < K и 0 иначе (:109), Nq k — число 2^k как рациональное. walsh_rec_partial_sum : (K <= pow2 k)%nat -> walsh_rec k K f m == q_sum (fun i => ' + HF + ' i * had k i m) K / Nq k (:119) — тот же сигнал как K-членная частичная сумма разложения по функциям Уолша. ' + CL + '.';
const N_ERR = 'walsh_compression_error : forall k f K, (K <= pow2 k)%nat -> Nq k * seq_inner (fun m => f m - walsh_rec k K f m) (fun m => f m - walsh_rec k K f m) (pow2 k) == q_sum (fun i => ' + HF + ' (K + i)%nat * ' + HF + ' (K + i)%nat) (pow2 k - K)%nat (:191): N·‖f − f_K‖² равно сумме квадратов сырых коэффициентов с номерами от K до N − 1; walsh_rec k K f (:114) — сигнал, восстановленный по первым K коэффициентам. Выведено из walsh_HH (ProcessFourierON.v:61), parseval_walsh (ProcessFourierON.v:91) и dropped_energy (:153). ' + CL + '.';
const N_TEQ = 'walsh_tail_eq : forall k f K, (K <= pow2 k)%nat -> q_sum (fun i => ' + HF + ' (K + i)%nat * ' + HF + ' (K + i)%nat) (pow2 k - K)%nat == Nq k * seq_inner f f (pow2 k) - captured (' + HF + ') K (:220) — равенство, из truncation_error_eq и parseval_walsh. Следствие walsh_compression_error_energy : Nq k * ‖f − walsh_rec k K f‖² == Nq k * seq_inner f f (pow2 k) - captured (' + HF + ') K (:234). ' + CL + '.';
const N_MONO = "walsh_compression_error_mono : forall k f K K', (K <= K')%nat -> (K' <= pow2 k)%nat -> seq_inner (fun m => f m - walsh_rec k K' f m) (fun m => f m - walsh_rec k K' f m) (pow2 k) <= seq_inner (fun m => f m - walsh_rec k K f m) (fun m => f m - walsh_rec k K f m) (pow2 k) (:244) — нестрогое неравенство: ошибка не возрастает. " + CL + '.';
const N_LOSS = 'walsh_bandlimited_lossless : forall k f K, (forall i, (K <= i < pow2 k)%nat -> ' + HF + ' i == 0) -> forall m, (m < pow2 k)%nat -> walsh_rec k K f m == f m (:260): если отброшенные сырые коэффициенты нулевые, восстановленный сигнал совпадает с исходным во всех точках. ' + CL + '.';
const N_LIFF = 'walsh_lossless_iff : forall k f K, (K <= pow2 k)%nat -> (forall m, (m < pow2 k)%nat -> walsh_rec k K f m == f m) <-> (forall i, (K <= i < pow2 k)%nat -> ' + HF + ' i == 0) (:274). ' + CL + '.';
const N_NORM = 'walsh_normalized_error_is_tail : forall (k : nat) (s : Q), s * s == inject_Z (Z.of_nat (pow2 k)) -> forall f K, (K <= pow2 k)%nat -> ferr (walsh_n k s) f (pow2 k) K == q_sum (fun i => seq_inner (walsh_n k s (K + i)%nat) f (pow2 k) * seq_inner (walsh_n k s (K + i)%nat) f (pow2 k)) (pow2 k - K)%nat (:302), где walsh_n k s i m = had k i m / s (ProcessOrthogonalWalsh.v:385), ferr e f N K — ‖f − P_K‖² (ProcessOrthonormalFourier.v:264). walsh_4j_error_is_tail (:316) — то же при k = 2j и s = 2^j, без посылки. Рациональное s с s² = 2^k существует в точности при чётном k: walsh_rational_norm_iff_even (ProcessOrthogonalWalsh.v:512). ' + CL + '.';
const N_FEB = 'fourier_error_is_tail_b (ProcessOrthonormalFourier.v:365): для системы, ортонормированной на первых K0 номерах, — (K <= K0)%nat -> captured cf K0 == seq_inner f f N -> ferr e f N K == q_sum (fun i => seq_inner (e (K + i)%nat) f N * seq_inner (e (K + i)%nat) f N) (K0 - K)%nat; вторая посылка — равенство Парсеваля на K0 коэффициентах. ' + CL + '.';
const N_CINV = 'walsh_convolution_inverse : forall k f g n, (n < pow2 k)%nat -> Nq k * dconv f g (pow2 k) n == op_apply (had k) (fun i => ' + HF + ' i * op_apply (had k) g (pow2 k) i) (pow2 k) n (:333); convolution_via_fwht : forall k f g n, (n < pow2 k)%nat -> dconv f g (pow2 k) n == fwht k (fun i => fwht k f i * fwht k g i) n / Nq k (:344). Из walsh_HH (ProcessFourierON.v:61), walsh_convolution (ProcessWalshConvolutionGeneral.v:193) и fwht_correct (ProcessFastWalsh.v:61). ' + CL + '.';
const N_CDEF = 'Fixpoint fwht_c (k : nat) (l : list Q) : list Q * nat (ProcessFastWalshCost.v:57): при k = 0 — (l, 0); на шаге S k′ — считает обе половины списка, складывает и вычитает их поэлементно (zipw, :50) и прибавляет к счёту длины списков сумм и разностей. Вторая компонента — число выполненных сложений и вычитаний рациональных чисел. ' + CL + '.';
const N_COST = 'fwht_c_ops : forall k l, length l = pow2 k -> snd (fwht_c k l) = (k * pow2 k)%nat (ProcessFastWalshCost.v:119) — равенство в nat, для всякого k и всякого списка длины 2^k. Считаются сложения и вычитания рациональных чисел в одной записи алгоритма (fwht_c, :57); операции со списками (firstn, skipn, ++) и стоимость рациональной арифметики в счёт не входят. ' + CL + '.';
const N_CVAL = 'fwht_c_correct : forall k l, length l = pow2 k -> forall i, (i < pow2 k)%nat -> nth i (fst (fwht_c k l)) 0 == fwht k (fun j => nth j l 0) i (ProcessFastWalshCost.v:148); fwht_c_cost_and_value : forall k l, length l = pow2 k -> snd (fwht_c k l) = (k * pow2 k)%nat ' + AND + ' forall i, (i < pow2 k)%nat -> nth i (fst (fwht_c k l)) 0 == op_apply (had k) (fun j => nth j l 0) (pow2 k) i (:186). ' + CL + '.';
const N_C8 = 'Example fwht_c_8 : fwht_c 3 [1; 2; 3; 4; 5; 6; 7; 8] = ([36; -4; -8; 0; -16; 0; 0; 0], 24%nat) (ProcessFastWalshCost.v:197) — вычислением (vm_compute); 24 = 3 · 8. ' + CL + '.';
const N_NOCLASS = 'статус: теорем об асимптотике, о нижней оценке числа операций и о числе операций матричного преобразования в src нет (поиск по ProcessFastWalsh.v, ProcessFastWalshCost.v); доказан точный счёт одной записи алгоритма — fwht_c_ops (ProcessFastWalshCost.v:119).';

{
  const { fix, add, save } = open('part07-ch05');

  // ------------------------------------------------------------ основной текст: «Что доказано — и что граница»
  fix('Доказано над ℚ, без аксиом.[^1]', null, { assumptions: 'все 49 объявлений шести файлов: ' + CL,
    note: DONE + ': опорных файлов стало шесть. В них 43 строки Qed (6 + 2 + 2 + 7 + 16 + 10) и шесть определений (captured, fwht, spec_trunc, walsh_rec, zipw, fwht_c); строк Axiom, Parameter, Admitted, разделов и посылок Hypothesis нет. Print Assumptions всех 49 объявлений — ' + CL + '.' });
  const C22 = 'Ошибка усечения по первым $K$ коэффициентам равна сумме квадратов отброшенных и монотонна по $K$;';
  fix('Ошибка усечения по первым $K$ коэффициентам равна сумме квадратов', 'truncation_error_eq', { theorem: 'walsh_compression_error', file: WR, assumptions: CL,
    note: KEPT + 'было доказано только расщепление суммы квадратов произвольной последовательности (truncation_error_eq, ProcessFourierCompression.v:61); восстановленного сигнала и ошибки как нормы разности не было. Теперь: ' + N_ERR + ' В нормированной шкале — ' + N_NORM });
  add({ theorem: 'walsh_compression_error_mono', file: WR, page_price: 'без аксиом', assumptions: CL, claim: C22, note: N_MONO });
  fix('для Уолша она контролируется равенством Планшереля;', 'walsh_captured_le_energy', { theorem: 'walsh_compression_error_energy', file: WR, assumptions: CL,
    note: KEPT + 'прежняя опора — walsh_captured_le_energy (ProcessFourierCompression.v:79), односторонняя оценка захваченной энергии; об ошибке в ней утверждения нет. Теперь: ' + N_TEQ });
  fix('*полосно-ограниченный* сигнал (спектр в первых $K$ модах) восстанавливается', 'walsh_compaction', { theorem: 'walsh_bandlimited_lossless', file: WR, assumptions: CL,
    note: KEPT + 'прежняя опора — walsh_compaction (ProcessWalshCompaction.v:41), равенство двух частичных сумм квадратов произвольной последовательности. Теперь: ' + N_LOSS + ' Обратное — ' + N_LIFF });

  // ------------------------------------------------------------ «Чего глава не утверждает» (правка 6)
  const C29 = L('Сложность $O(N§log N)$ сама по себе — операционное свойство (счёт шагов), а не равенственное тождество; доказано *равенство* быстрого и матричного преобразований, а счёт шагов — для одной записи алгоритма: бабочка на списке делает ровно $k§cdot2^k$ сложений и вычитаний.');
  fix(L('Сложность $O(N§log N)$ сама по себе — операционное'), 'fwht_correct', { claim: C29, assumptions: CL,
    note: DONE + ': было «…а не оценка стоимости» — после добавления ProcessFastWalshCost.v счёт шагов одной записи алгоритма доказан, и страница называет его. Равенство — fwht_correct : forall k f i, (i < pow2 k)%nat -> fwht k f i == op_apply (had k) f (pow2 k) i (ProcessFastWalsh.v:61). ' + CL + '.' });
  add({ theorem: 'fwht_c_ops', file: CO, assumptions: CL, claim: C29, note: N_COST + ' ' + N_CVAL });
  add({ theorem: null, file: null, claim: 'Оценка стоимости как класса — асимптотика, оптимальность, сравнение с матричным счётом — остаётся вне доказанного.', note: N_NOCLASS });

  // ------------------------------------------------------------ каркас главы
  const C43 = 'Ошибка сжатия = сумма квадратов отброшенных коэффициентов (монотонна);';
  fix('Ошибка сжатия = сумма квадратов', 'truncation_error_eq', { theorem: 'walsh_compression_error', file: WR, assumptions: CL, note: KEPT + N_ERR });
  add({ theorem: 'walsh_compression_error_mono', file: WR, assumptions: CL, claim: C43, note: N_MONO });

  // ------------------------------------------------------------ § «Ошибка сжатия есть отброшенная энергия»
  const C60 = 'Качество сжатия — это ошибка восстановления, и она в точности есть *отброшенная хвостовая энергия*:';
  fix('Качество сжатия — это ошибка восстановления', 'truncation_error_eq', { theorem: 'walsh_compression_error', file: WR, assumptions: CL,
    note: KEPT + 'формула страницы записана в нормированной шкале; ниже страница оговаривает сырую шкалу Уолша с масштабом N. Сырая шкала: ' + N_ERR + ' Нормированная шкала: ' + N_NORM });
  add({ theorem: 'walsh_normalized_error_is_tail', file: WR, assumptions: CL, claim: C60, note: N_NORM });
  add({ theorem: 'walsh_normalized_error_is_tail', file: WR, assumptions: CL, claim: 'так что ошибка равна второй сумме — ровно тому, что усечение выкинуло.[^2]',
    note: 'Вторая сумма формулы — сумма квадратов нормированных коэффициентов с номерами от K до N − 1. ' + N_NORM + ' Для всякой полной ортонормированной системы — ' + N_FEB });
  add({ theorem: 'walsh_compression_error_mono', file: WR, assumptions: CL, claim: L('Захваченная энергия монотонно растёт с $K$ (а ошибка убывает) — то же свойство, что несло конечное ядро сходимости в Главе 7.4.'),
    note: '«Ошибка убывает» — в нестрогом смысле: ' + N_MONO });
  fix('Оговорка о шкале: здесь $c_i$ — коэффициенты в *нормированной*', 'parseval_walsh', {
    note: 'Theorem parseval_walsh : forall k f, seq_inner (Hf) (Hf) (pow2 k) == inject_Z (Z.of_nat (pow2 k)) * seq_inner f f (pow2 k) (ProcessFourierON.v:91) — для всякого k. Формула в сырой шкале (N‖f‖² = захвачено + отброшено) записана теоремой с 18.11: ' + N_TEQ });
  const C76 = L('Точнее: если $f_K$ — сигнал, восстановленный по первым $K$ сырым коэффициентам (обратным шагом $H/N$ от спектра, в котором коэффициенты с номерами $i§ge K$ заменены нулями), то $N§norm{f-f_K}^2=§sum_{K§le i<N}(Hf)_i^2$.');
  add({ theorem: 'walsh_compression_error', file: WR, assumptions: CL, claim: C76, note: N_ERR });
  add({ theorem: 'walsh_rec', file: WR, assumptions: CL, claim: C76, note: N_REC });
  const C79 = 'Нормированная шкала у Уолша рациональна при чётном $k$, и тогда формула верна в ней дословно.';
  add({ theorem: 'walsh_4j_error_is_tail', file: WR, assumptions: CL, claim: C79, note: N_NORM });
  add({ theorem: 'walsh_rational_norm_iff_even', file: OW, assumptions: CL, claim: C79,
    note: 'walsh_rational_norm_iff_even : forall k : nat, (exists s : Q, s * s == inject_Z (Z.of_nat (pow2 k))) <-> Nat.Even k (ProcessOrthogonalWalsh.v:512); сторона «нечётное — нет» — walsh_odd_no_rational_norm (:492), сторона «чётное — есть» — walsh_even_norm_exists (:464). ' + CL + '.' });

  // ------------------------------------------------------------ § «Полосно-ограниченный сигнал»
  fix('Если спектр сигнала *сосредоточен*', 'walsh_compaction', { theorem: 'walsh_bandlimited_lossless', file: WR, assumptions: CL,
    note: KEPT + 'прежняя опора — walsh_compaction (ProcessWalshCompaction.v:41), равенство энергий для произвольной последовательности; что первые K коэффициентов восстанавливают сигнал, доказано не было. Теперь: ' + N_LOSS + ' Обратное — ' + N_LIFF + ' Условие страницы c_i = 0 при i >= K для нормированных и для сырых коэффициентов одно и то же (они отличаются ненулевым множителем).' });
  add({ theorem: 'walsh_compaction', file: WC, assumptions: CL, claim: 'захваченная энергия совпадает с полной.[^3]',
    note: 'Theorem walsh_compaction : forall (c : nat -> Q) (K N : nat), (K <= N)%nat -> (forall i, (K <= i < N)%nat -> c i == 0) -> captured c N == captured c K (ProcessWalshCompaction.v:41). ' + CL + '.' });
  const C98 = '*Ошибка сжатия = отброшенная энергия — точное рациональное тождество (для Уолша), а полосно-ограниченный сигнал сжимается без потерь.';
  fix('*Ошибка сжатия = отброшенная энергия — точное рациональное тождество', 'truncation_error_eq', { theorem: 'walsh_compression_error', file: WR, assumptions: CL, note: KEPT + N_ERR });
  add({ theorem: 'walsh_bandlimited_lossless', file: WR, assumptions: CL, claim: C98, note: N_LOSS });

  // ------------------------------------------------------------ § «Быстрое преобразование» (правка 7)
  fix('Но рекурсивная структура Сильвестра (Глава 7.2) даёт *бабочку*', 'fwht', {
    note: "Fixpoint fwht (ProcessFastWalsh.v:41): на шаге S k' при i < 2^k' — сумма преобразований двух половин, при i >= 2^k' — их разность в точке i − 2^k'. Счёт операций ведётся с 18.11 для записи на списке: " + N_COST + ' k·2^k = N·log₂N при N = 2^k; оценка O(N log N) как класс и число операций матричного преобразования теоремами не записаны — страница оговаривает это (стр. 29–33).' });
  add({ theorem: 'fwht_c_ops', file: CO, assumptions: CL, claim: L('Но рекурсивная структура Сильвестра (Глава 7.2) даёт *бабочку*: преобразование размера $2N$ собирается из двух преобразований половин сложениями и вычитаниями ($§text{lo}+§text{hi}$ и $§text{lo}-§text{hi}$), а это — $O(N§log N)$ операций.'), note: N_COST });
  const C114 = L('*Быстрый Уолш — процесс-алгоритм, доказанно равный матричному преобразованию (точно над ℚ, все $2^k$). Сама оценка $O(N§log N)$ — операционное свойство (счёт шагов), читается поверх доказанного равенства, но не входит в равенственное ядро; для бабочки на списке сам счёт доказан: ровно $k§cdot2^k$ сложений и вычитаний.*');
  fix('*Быстрый Уолш — процесс-алгоритм, доказанно равный матричному преобразованию', 'fwht_correct', { claim: C114, assumptions: CL,
    note: DONE + ': добавлены слова о доказанном счёте. Равенство — fwht_correct (ProcessFastWalsh.v:61), все k. ' + CL + '.' });
  add({ theorem: 'fwht_c_ops', file: CO, assumptions: CL, claim: C114, note: N_COST + ' ' + N_CVAL });

  // ------------------------------------------------------------ § «Свёртка»
  const C137 = L('Поскольку ненормированный Уолш удовлетворяет $H^2=N§cdot I$, обратный шаг есть $H/N$: преобразовать $f,g$, перемножить спектры, применить $H$ и разделить на $N$; с быстрым Уолшем всё это — $O(N§log N)$.');
  fix(L('Поскольку ненормированный Уолш удовлетворяет $H^2=N§cdot I$'), 'walsh_HH', {
    note: 'Theorem walsh_HH : forall k f m, (m < pow2 k)%nat -> op_apply (had k) (op_apply (had k) f (pow2 k)) (pow2 k) m == inject_Z (Z.of_nat (pow2 k)) * f m (ProcessFourierON.v:61). Формула свёртки через преобразование записана теоремой с 18.11: ' + N_CINV + ' Число операций всей свёртки теоремой не записано; для одного быстрого преобразования на списке — fwht_c_ops (ProcessFastWalshCost.v:119).' });
  add({ theorem: 'convolution_via_fwht', file: WR, assumptions: CL, claim: C137, note: N_CINV });

  // ------------------------------------------------------------ разбор и закрытие части
  const C160 = 'ошибка сжатия $=$ отброшенная энергия (монотонна по $K$);';
  fix('ошибка сжатия $=$ отброшенная энергия (монотонна по $K$);', 'truncation_error_eq', { theorem: 'walsh_compression_error', file: WR, assumptions: CL, note: KEPT + N_ERR });
  add({ theorem: 'walsh_compression_error_mono', file: WR, assumptions: CL, claim: C160, note: N_MONO });
  fix('| ошибка $=$ отброшенная энергия; полосно-огр.', 'truncation_error_eq', { theorem: 'walsh_compression_error', file: WR, assumptions: CL,
    note: KEPT + 'первый пункт строки — ' + N_ERR + ' Остальные три пункта отвечают теоремам walsh_compaction (ProcessWalshCompaction.v:41), fwht_correct (ProcessFastWalsh.v:61), walsh_convolution (ProcessWalshConvolutionGeneral.v:193).' });
  fix('сжатие с точной ошибкой,', 'truncation_error_eq', { theorem: 'walsh_compression_error', file: WR, assumptions: CL, note: KEPT + N_ERR });
  fix('Честные P4-границы, помеченные и не выданные за большее', null, {
    note: 'Пометки стоят в шапках файлов (ProcessFourierON.v:15–18, ProcessFastWalsh.v:16–17, ProcessWalshCompaction.v:14–16, ProcessWalshConvolutionGeneral.v:15–16); доказанным ничего из перечня не названо. «Рациональна лишь при чётном k» — теорема walsh_rational_norm_iff_even (ProcessOrthogonalWalsh.v:512). «Сложность O(N log N) как метаоценка»: класс и асимптотика теоремами не записаны; доказан точный счёт одной записи алгоритма — fwht_c_ops (ProcessFastWalshCost.v:119), страница говорит об этом на стр. 29–33.' });
  add({ theorem: 'walsh_rational_norm_iff_even', file: OW, assumptions: CL, claim: L('нормировка $1/§sqrt N$ (рациональна лишь при чётном $k$),'),
    note: 'walsh_rational_norm_iff_even : forall k : nat, (exists s : Q, s * s == inject_Z (Z.of_nat (pow2 k))) <-> Nat.Even k (ProcessOrthogonalWalsh.v:512). ' + CL + '.' });

  // ------------------------------------------------------------ сноска 1
  fix('`ProcessWalshCompaction.v` (1),', null, { claim: '`ProcessWalshCompaction.v` (2),', assumptions: 'оба объявления файла: ' + CL,
    note: DONE + ': было «(1)» — число из шапки файла. В файле 2 строки Qed: теорема walsh_compaction (:41) и пример compaction_4_example (:58).' }, WC);
  fix('`ProcessWalshConvolutionGeneral.v` (7);', null, { claim: '`ProcessWalshConvolutionGeneral.v` (7),' }, WG);
  add({ theorem: null, file: WR, page_price: '0 аксиом', assumptions: 'все 18 объявлений файла: ' + CL, claim: '`ProcessWalshReconstruction.v` (16),',
    note: 'В ProcessWalshReconstruction.v 16 строк Qed и два определения (spec_trunc, walsh_rec); Admitted, Axiom, Parameter нет (слово Admitted — только в строке STATUS шапки); все 18 объявлений — ' + CL + '.' });
  add({ theorem: null, file: CO, page_price: '0 аксиом', assumptions: 'все 12 объявлений файла: ' + CL, claim: '`ProcessFastWalshCost.v` (10);',
    note: 'В ProcessFastWalshCost.v 10 строк Qed и два определения (zipw, fwht_c); Admitted, Axiom, Parameter нет (слово Admitted — только в строке STATUS шапки); все 12 объявлений — ' + CL + '.' });
  fix('все 0 `Admitted`, 0 аксиом.', 'Admitted', {
    note: '`Admitted` — ключевое слово Rocq, не имя объявления (инструмент показывает его как имя без объявления). В шести файлах слово встречается только в строке STATUS шапки-комментария; незавершённых доказательств, строк Axiom и Parameter нет; Print Assumptions всех 49 объявлений — ' + CL + '.' });

  // ------------------------------------------------------------ сноска 2
  fix('`truncation_error_eq` даёт баланс', 'truncation_error_eq', { assumptions: CL,
    claim: '`truncation_error_eq` даёт баланс `captured`$(c,N)=$`captured`$(c,K)+$хвост для любой последовательности $c$;',
    note: DONE + ': добавлено «для любой последовательности c». Lemma truncation_error_eq : forall (c : nat -> Q) (K N : nat), (K <= N)%nat -> captured c N == captured c K + q_sum (fun i => c (K + i)%nat * c (K + i)%nat) (N - K)%nat (ProcessFourierCompression.v:61). ' + CL + '.' });
  const F2b = 'Что хвост есть ошибка восстановления, доказано в `ProcessWalshReconstruction.v`: `walsh_rec` — сигнал $f_K$, восстановленный по первым $K$ сырым коэффициентам (он же частичная сумма разложения по функциям Уолша, `walsh_rec_partial_sum`);';
  add({ theorem: 'walsh_rec', file: WR, page_price: '0 аксиом', assumptions: CL, claim: F2b, note: N_REC });
  add({ theorem: 'walsh_rec_partial_sum', file: WR, page_price: '0 аксиом', assumptions: CL, claim: F2b, note: N_REC });
  add({ theorem: 'walsh_compression_error', file: WR, page_price: '0 аксиом', assumptions: CL, claim: L('`walsh_compression_error` — $N§norm{f-f_K}^2=§sum_{K§le i<N}(Hf)_i^2$;'), note: N_ERR });
  const F2d = L('`walsh_tail_eq` — эта сумма равна $N§norm{f}^2-$`captured`$(Hf,K)$ (равенство, по Планшерелю; `walsh_captured_le_energy` — оценка захваченной энергии сверху);');
  fix('Для Уолша полная энергия есть', 'walsh_captured_le_energy', { claim: F2d, assumptions: CL,
    note: DONE + ': было «ошибка контролируется Парсевалем — walsh_captured_le_energy»; теперь теорема названа тем, что она утверждает. Theorem walsh_captured_le_energy : forall k f K, (K <= pow2 k)%nat -> captured (op_apply (had k) f (pow2 k)) K <= inject_Z (Z.of_nat (pow2 k)) * seq_inner f f (pow2 k) (ProcessFourierCompression.v:79) — оценка захваченной энергии сверху. ' + CL + '.' });
  add({ theorem: 'walsh_tail_eq', file: WR, page_price: '0 аксиом', assumptions: CL, claim: F2d, note: N_TEQ });
  add({ theorem: 'walsh_compression_error_mono', file: WR, page_price: '0 аксиом', assumptions: CL, claim: '`walsh_compression_error_mono` — ошибка не возрастает по $K$.', note: N_MONO });
  const F2f = 'В нормированной шкале: для полной ортонормированной системы — `fourier_error_is_tail_b` (Глава 7.4); для Уолша при рациональном $s$ с $s^2=N$ — `walsh_normalized_error_is_tail`, при $N=4^j$ — `walsh_4j_error_is_tail`. 0 аксиом.';
  add({ theorem: 'fourier_error_is_tail_b', file: OF, page_price: '0 аксиом', assumptions: CL, claim: F2f, note: N_FEB });
  add({ theorem: 'walsh_normalized_error_is_tail', file: WR, page_price: '0 аксиом', assumptions: CL, claim: F2f, note: N_NORM });
  add({ theorem: 'walsh_4j_error_is_tail', file: WR, page_price: '0 аксиом', assumptions: CL, claim: F2f, note: N_NORM });

  // ------------------------------------------------------------ сноска 3
  add({ theorem: 'walsh_bandlimited_lossless', file: WR, page_price: '0 аксиом', assumptions: CL,
    claim: L('`walsh_bandlimited_lossless` в `ProcessWalshReconstruction.v`: если $(Hf)_i=0$ при $K§le i<N$, то $f_K(m)=f(m)$ при всех $m<N$;'), note: N_LOSS });
  add({ theorem: 'walsh_lossless_iff', file: WR, page_price: '0 аксиом', assumptions: CL,
    claim: 'обратное — `walsh_lossless_iff`: восстановление точно тогда и только тогда, когда отброшенные коэффициенты равны нулю.', note: N_LIFF });
  fix('`walsh_compaction` в `ProcessWalshCompaction.v`: при $c_i=0$', 'walsh_compaction', { assumptions: CL,
    claim: L('Равенство энергий — `walsh_compaction` в `ProcessWalshCompaction.v`: при $c_i=0$ для $K§le i<N$ выполнено `captured`$(c,N)=$`captured`$(c,K)$ — хвост нулевой. 0 аксиом.'),
    note: DONE + ': теорема названа равенством энергий; восстановление — walsh_bandlimited_lossless. Сноска передаёт утверждение точно (ProcessWalshCompaction.v:41; ещё посылка K <= N). Предмет теоремы — произвольная последовательность c. ' + CL + '.' });

  // ------------------------------------------------------------ сноска 4 (правка 8)
  const F4b = 'Счёт шагов — в `ProcessFastWalshCost.v` (10 утверждений, 0 аксиом): `fwht_c` — бабочка на списке из $2^k$ рациональных чисел, возвращающая результат вместе с числом выполненных сложений и вычитаний;';
  add({ theorem: 'fwht_c', file: CO, page_price: '0 аксиом', assumptions: CL, claim: F4b, note: N_CDEF });
  const F4c = L('это число равно $k§cdot2^k$ (`fwht_c_ops`), значения совпадают с `fwht` (`fwht_c_correct`) и с матричным преобразованием (`fwht_c_cost_and_value`);');
  add({ theorem: 'fwht_c_ops', file: CO, page_price: '0 аксиом', assumptions: CL, claim: F4c, note: N_COST });
  add({ theorem: 'fwht_c_correct', file: CO, page_price: '0 аксиом', assumptions: CL, claim: F4c, note: N_CVAL });
  add({ theorem: 'fwht_c_cost_and_value', file: CO, page_price: '0 аксиом', assumptions: CL, claim: F4c, note: N_CVAL });
  add({ theorem: 'fwht_c_8', file: CO, page_price: '0 аксиом', assumptions: CL, claim: 'пример $N=8$, 24 операции — `fwht_c_8`.', note: N_C8 });
  add({ theorem: null, file: null, claim: 'Операции со списками и стоимость рациональной арифметики не считаются; оптимальность и сравнение с матричным счётом не утверждаются.',
    note: 'статус: так и есть. Счётчик в fwht_c (ProcessFastWalshCost.v:57) растёт только на длины списков сумм и разностей; firstn, skipn и ++ в него не входят; размер числителей и знаменателей не учитывается. ' + N_NOCLASS });

  // ------------------------------------------------------------ сноска 5
  const F5a = L('Доказательство опирается на характерное свойство Уолша (`had_character`, Глава 7.2) и на переиндексацию конечной суммы под XOR-биекцией ($§texttt{xor§_perm§_q§_sum}$, доказанную блочной рекурсией Сильвестра).');
  fix('Доказательство опирается на характерное свойство Уолша', 'had_character', { claim: F5a }, WCH);
  fix('Доказательство опирается на характерное свойство Уолша', 'xor_perm_q_sum', { claim: F5a }, WG);
  const F5b = L('Обратный шаг — `walsh_convolution_inverse` в `ProcessWalshReconstruction.v`: $N§,(f§ast g)=H§bigl((Hf)§cdot(Hg)§bigr)$; то же через быструю бабочку — `convolution_via_fwht`. 0 аксиом.');
  add({ theorem: 'walsh_convolution_inverse', file: WR, page_price: '0 аксиом', assumptions: CL, claim: F5b, note: N_CINV });
  add({ theorem: 'convolution_via_fwht', file: WR, page_price: '0 аксиом', assumptions: CL, claim: F5b, note: N_CINV });
  save();
}
