// Часть VI, шаг 6, страницы (2026-11-15, слово автора «Делай»): 4 правки главы VI.6 внесены
// (фраза о гамильтониане, абзац о пространстве Фока, сноски 1 и 9).
// Формализация — новый src/process/ProcessLadderRational.v; прежние файлы не менялись.
// Запуск: node patch-p06-step-06-pages.cjs  (затем relocate + merge по part06-ch06). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 15.11 (Часть VI, шаг 6, слово автора)';
const BYF = DONE + ' (формализацией; текст страницы не менялся)';
const CL = 'Closed under the global context';
const LR = 'src/process/ProcessLadderRational.v';
const HL = 'src/process/ProcessHarmonicLadder.v';
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

// утверждения нового файла (номера строк — src/process/ProcessLadderRational.v)
const N_DEF = 'Definition gann (psi : nat -> Q) : nat -> Q := fun n => al (S n) * psi (S n) (:86); gcre psi n := match n with O => 0 | S m => be (S m) * psi m end (:89); посылка раздела GenLadder — Hab : forall n, al n * be n == inject_Z (Z.of_nat n).';
const N_UNSAT = 'ladder_premise_unsatisfiable : forall s : nat -> Q, (forall n, s n * s n == inject_Z (Z.of_nat n)) -> False (:69) — через no_rational_sqrt2 (analysis/Sqrt2Irrational.v): s 2 был бы рациональным корнем из двух. ' + CL + '.';
const N_GCOMM = 'gcommutator_canonical : forall psi n, gann (gcre psi) n - gcre (gann psi) n == psi n (:114) — при al n * be n == n, на всех последовательностях nat -> Q. ' + N_DEF + ' ' + CL + '.';
const N_CCR = 'commutator_canonical_rational : forall psi n, gann al1 (gcre be1 psi) n - gcre be1 (gann al1 psi) n == psi n (:256), где al1 n := inject_Z (Z.of_nat n), be1 n := 1 (:250, :251) — без посылок. ' + CL + '.';
const N_NUM = 'number_operator_rational : forall psi n, gcre be1 (gann al1 psi) n == ProcessHarmonicLadder.num psi n (:260); для любых весов — gcre_gann_eq_num (:93). ' + CL + '.';
const N_HAM = 'gham_from_ladder : forall psi n, gcre (gann psi) n + (1 # 2) * psi n == ProcessHarmonicLadder.ham psi n (:124) — (a†a + ½)ψ = Hψ; на состояниях |n⟩ — gham_ladder_eigen (:133). ' + CL + '.';
const N_HAMR = 'ham_rational_eigen : forall n m, gcre be1 (gann al1 (ket n)) m + (1 # 2) * ket n m == energy n * ket n m (:264) — формула уровней как следствие лестницы, без посылок. ' + CL + '.';
const N_KETS = 'gann_ket_S : gann (ket (S n)) m == al (S n) * ket n m (:143); gann_ket_O : gann (ket 0) m == 0 (:152); gcre_ket : gcre (ket n) m == be (S n) * ket (S n) m (:157). ' + CL + '.';
const N_ADJ = 'ladder_adjoint_factorial : forall psi phi K, q_sum (fun n => fq n * gann al1 psi n * phi n) K == q_sum (fun n => fq n * psi n * gcre be1 phi n) (S K) (:282), где fq n — n! (:271); общий вид для веса w с w (S n) * be (S n) == w n * al (S n) — ladder_adjoint_weighted (:170). ' + CL + '.';
const N_TRB = 'truncated_commutator_below_top : forall K psi n, S n < K -> tann K (tcre K psi) n - tcre K (tann K psi) n == psi n (:216); trunc K psi n := if n <? K then psi n else 0 (:191), tann, tcre — лестница усечения (:193, :194); для рациональной реализации — truncated_rational_below_top (:288). ' + CL + '.';
const N_TRT = 'truncated_commutator_top : forall k psi, tann (S k) (tcre (S k) psi) k - tcre (S k) (tann (S k) psi) k == - inject_Z (Z.of_nat k) * psi k (:233) — на верхнем уровне усечения до K = k + 1 уровней коммутатор равен −(K − 1); для рациональной реализации — truncated_rational_top (:292). ' + CL + '.';

{
  const { fix, note, add, save } = open('part06-ch06');
  const P199 = '**Осциллятор — образец бесконечномерной наблюдаемой в ToS:** каноническая алгебра';

  // --- основной текст, не менялся (места 6.1–6.3)
  fix(L('каноническое $[a,a^§dagger]=1$ для лестницы осциллятора и его бесконечный спектр;'), 'commutator_canonical', { theorem: 'commutator_canonical_rational', file: LR,
    note: BYF + ', сноска 9 переписана: было — commutator_canonical (ProcessHarmonicLadder.v:137) под невыполнимой посылкой s n * s n == n. ' + N_CCR + ' На конечных стадиях — усечения: ' + N_TRB + ' Бесконечный спектр — energy_unbounded (ProcessHarmonicLadder.v:93).' });
  fix('Первый *бесконечномерный* квантовый объект — гармонический осциллятор — реализует каноническую алгебру', 'commutator_canonical', { theorem: 'commutator_canonical_rational', file: LR,
    note: BYF + ': ' + N_CCR + ' ' + N_GCOMM + ' Сопряжённость a и a† — ' + N_ADJ });
  fix('Пространство состояний осциллятора — *пространство Фока* — удерживается процессно: как процесс конечных усечений', 'FockState', { theorem: 'truncated_commutator_below_top', file: LR,
    note: DONE + ' (формализацией; следом добавлена фраза о коммутаторе усечения): было — усечений в формализации не было. ' + N_TRB + ' ' + N_TRT });
  fix(P199, 'commutator_canonical', { theorem: 'commutator_canonical_rational', file: LR,
    note: BYF + ': каноническая алгебра — ' + N_CCR + ' ' + N_NUM });
  fix(P199, 'ham_eigenvalue', { theorem: 'ham_rational_eigen', file: LR,
    note: BYF + ': было — формула уровней задана определением и с лестницей не связана. ' + N_HAMR + ' ' + N_HAM + ' Неограниченность — energy_unbounded (ProcessHarmonicLadder.v:93).' });
  fix('Разбор показывает, что операторная теория на $L^2$ в ToS — процессная: правила', 'commutator_canonical', { theorem: 'commutator_canonical_rational', file: LR,
    note: BYF + ': в части «каноническая лестница … на конечных стадиях» — ' + N_CCR + ' ' + N_TRB + ' Об энергии и спектре диагонального оператора в том же перечне — записи стр. 29 и 99 (шаг 7).' });
  note(L('Здесь «бесконечный спектр» означает *формулу уровней* $E_n=n+§tfrac12$ как процесс по $n$'), 'energy',
    'Оговорка страницы точна: Definition energy (n : nat) : Q := inject_Z (Z.of_nat n) + (1 # 2) (ProcessHarmonicLadder.v:55); ham_eigenvalue (:72): ham (ket n) m == energy n * ket n m. Что формула уровней следует из лестницы — ham_rational_eigen (' + LR + ':264, шаг 6). Одноимённое определение energy есть в ProcessEnergyConservation.v:50 (другой предмет).');
  note('По шапкам файлов и синтез-файлу кластера — 0 аксиом; у ключевых теорем стоит `Print Assumptions`.', null,
    'Названные файлы существуют; строк Axiom, Parameter, Admitted в них нет; Qed в восьми прежних: 8, 6, 11, 8, 6, 5, 5, 3 (шапки совпадают со счётом), в ProcessLadderRational.v (добавлен в перечень 15.11, шаг 6) — 24. Для всех объявлений этих файлов (и для q_sum_swap) компилятор даёт ' + CL + '.');

  // --- правка 1: гамильтониан через лестницу (место 6.2)
  const C171 = L('Оператор числа $N=a^§dagger a$ считает кванты, а гамильтониан осциллятора $H=a^§dagger a+§tfrac12$ имеет спектр, растущий без границы:');
  fix(L('Оператор числа $N=a^§dagger a$ считает кванты, а гамильтониан осциллятора имеет спектр,'), 'cre_ann_eq_num', { theorem: 'number_operator_rational', file: LR, claim: C171,
    note: DONE + ': было «гамильтониан осциллятора имеет спектр» — гамильтониан был задан определением, с лестницей не связан; cre_ann_eq_num стояла под невыполнимой посылкой. ' + N_NUM });
  add({ theorem: 'gham_from_ladder', file: LR, claim: C171, note: N_HAM });

  // --- правка 2: абзац о пространстве Фока (места 6.1, 6.3)
  const CA = 'На усечении коммутатор равен единице на всех уровнях ниже верхнего, а на верхнем уровне равен $-(K-1)$: дефект усечения сидит на его краю и с ростом $K$ уходит вверх.';
  const CB = L('Иррациональный множитель $§sqrt n$, входящий в привычную запись лестничных операторов, в ToS не вводится: над ℚ числа $s$ с $s^2=2$ нет.');
  const CC = L('Его место занимают два рациональных веса с произведением $§alpha_n§beta_n=n$ — понижение умножает на $§alpha_n$, повышение на $§beta_n$; простейший выбор — $§alpha_n=n$, $§beta_n=1$.');
  const CD = L('Это запись в ненормированных состояниях, $§langle n|n§rangle=n!$: в скалярном произведении с весами $n!$ операторы $a$ и $a^§dagger$ взаимно сопряжены.');
  const CE = 'Лестничная алгебра от выбора весов не зависит, и в наблюдаемых — уровнях, шаге, коммутаторе — стоят одни рациональные величины.';
  fix(L('Иррациональный множитель $§sqrt n$, входящий в действие лестничных операторов, вводится *абстрактным параметром*'), 'commutator_canonical', {
    theorem: 'ladder_premise_unsatisfiable', file: LR, claim: CB,
    note: DONE + ': было «вводится абстрактным параметром $s$ с $s^2=n$» — такого рационального s нет, и теоремы раздела Ladder были верны впустую. ' + N_UNSAT });
  add({ theorem: 'truncated_commutator_below_top', file: LR, claim: CA, note: DONE + ' (добавлено): ' + N_TRB });
  add({ theorem: 'truncated_commutator_top', file: LR, claim: CA, note: N_TRT });
  add({ theorem: 'gcommutator_canonical', file: LR, claim: CC, note: DONE + ' (добавлено): ' + N_GCOMM });
  add({ theorem: 'gann_ket_S', file: LR, claim: CC, note: 'Действие на состояниях: ' + N_KETS });
  add({ theorem: 'al1_be1', file: LR, claim: CC, note: 'al1_be1 : forall n, al1 n * be1 n == inject_Z (Z.of_nat n) (:253) — посылка лестницы выполнена для al1 n = n, be1 n = 1. ' + CL + '.' });
  add({ theorem: 'ladder_adjoint_factorial', file: LR, claim: CD, note: DONE + ' (добавлено): ' + N_ADJ + ' «⟨n|n⟩ = n!» — чтение веса fq n.' });
  add({ theorem: 'gcommutator_canonical', file: LR, claim: CE, note: 'Коммутатор и оператор числа — для любых весов с al n * be n == n: gcommutator_canonical (:114), gcre_gann_eq_num (:93); уровни — gham_from_ladder (:124); шаг уровней — energy_spacing (ProcessHarmonicLadder.v:81). ' + CL + '.' });

  // --- правка 4: сноска 9
  const C9a = L('Лестница с рациональными весами — файл `ProcessLadderRational.v` (0 аксиом): `commutator_canonical_rational` ($[a,a^§dagger]=1$), `number_operator_rational` ($N=a^§dagger a$), `ham_rational_eigen` ($(a^§dagger a+§tfrac12)|n§rangle=(n+§tfrac12)|n§rangle$ — формула уровней как следствие лестницы), `ladder_adjoint_factorial` (сопряжённость $a$ и $a^§dagger$ с весами $n!$); для любых весов с $§alpha_n§beta_n=n$ — `gcommutator_canonical`, `gham_from_ladder`.');
  const C9b = 'Усечения: `truncated_commutator_below_top` и `truncated_commutator_top`.';
  const C9c = L('Свойства формулы уровней — `energy_spacing` (шаг $1$), `ground_energy` ($§tfrac12$) и `energy_unbounded` (спектр неограничен) в `ProcessHarmonicLadder.v` (0 аксиом).');
  const C9d = 'Прежние `commutator_canonical` и `cre_ann_eq_num` того же файла стоят под посылкой «рациональное $s$ с $s(n)^2=n$ при всех $n$», а такого $s$ нет (`ladder_premise_unsatisfiable`).';
  fix(L('`commutator_canonical` ($[a,a^§dagger]=1$), `cre_ann_eq_num`'), 'energy_spacing', { claim: C9c,
    note: 'energy_spacing (:81): forall n, energy (S n) - energy n == 1 — арифметика определения energy (:55). Одноимённое объявление есть в src/stdlib/OscillatorCorrection.v:42; глава называет ProcessHarmonicLadder.v. ' + CL + '.' });
  add({ theorem: 'ground_energy', file: HL, claim: C9c, page_price: '0 аксиом', note: 'ground_energy (:89): energy 0 == 1 # 2. ' + CL + '.' });
  add({ theorem: 'energy_unbounded', file: HL, claim: C9c, page_price: '0 аксиом', note: 'energy_unbounded (:93): forall B : Q, exists n, B < energy n. ' + CL + '.' });
  add({ theorem: 'commutator_canonical_rational', file: LR, claim: C9a, page_price: '0 аксиом', note: DONE + ': было — имена раздела Ladder под невыполнимой посылкой. ' + N_CCR });
  add({ theorem: 'number_operator_rational', file: LR, claim: C9a, page_price: '0 аксиом', note: N_NUM });
  add({ theorem: 'ham_rational_eigen', file: LR, claim: C9a, page_price: '0 аксиом', note: N_HAMR });
  add({ theorem: 'ladder_adjoint_factorial', file: LR, claim: C9a, page_price: '0 аксиом', note: N_ADJ });
  add({ theorem: 'gcommutator_canonical', file: LR, claim: C9a, page_price: '0 аксиом', note: N_GCOMM });
  add({ theorem: 'gham_from_ladder', file: LR, claim: C9a, page_price: '0 аксиом', note: N_HAM });
  add({ theorem: 'truncated_commutator_below_top', file: LR, claim: C9b, note: N_TRB });
  add({ theorem: 'truncated_commutator_top', file: LR, claim: C9b, note: N_TRT });
  add({ theorem: 'ladder_premise_unsatisfiable', file: LR, claim: C9d, note: N_UNSAT });
  add({ theorem: 'commutator_canonical', file: HL, claim: C9d,
    note: 'Theorem commutator_canonical (:137) — в разделе Ladder с посылкой Hs : forall n, s n * s n == inject_Z (Z.of_nat n) (:111), s : nat -> Q; сноска это говорит. ' + CL + '.' });
  add({ theorem: 'cre_ann_eq_num', file: HL, claim: C9d, note: 'Lemma cre_ann_eq_num (:121) — под той же посылкой Hs (:111). ' + CL + '.' });

  save();
}
