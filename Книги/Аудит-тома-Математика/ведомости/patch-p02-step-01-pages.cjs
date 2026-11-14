// Часть II, шаг 1, страницы (2026-11-13, слово автора «Вноси; А; А»): 6 правок главы II.1 о счёте внесены;
// развилка `ToS_nat` — А (слово оставлено, определение в CountingPresence.v); развилка «свидетель» — А
// (в восьми теоремах свидетель distinction_of True заменён на distinction_true_false; на страницах II.1 и II.2
// имя свидетеля заменено в двух местах, ещё два места II.2 ждут показа автору).
// Формализация — src/foundation/CountingPresence.v; правки доказательств в Distinction.v и PrimalityOfOne.v.
// Запуск: node patch-p02-step-01-pages.cjs  (затем relocate + merge по part02-ch01 и part02-ch02). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть II, шаг 1, слово автора)';
const F = 'src/foundation/';
const CP = F + 'CountingPresence.v';
const CL = 'Closed under the global context';
const BS = String.fromCharCode(92);
const GE = '$n ' + BS + 'ge 1$';
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();
const WIT = ' [13.11, Часть II, шаг 1: свидетель заменён на различение «истина | ложь» (distinction_true_false; в Distinction.v — тем же термом); теперь ' + CL + '.]';
const EIGHT = new Set(['one_distinction_exists', 'two_distinctions_exist', 'distinction_count_succ', 'distinction_count_any',
  'first_count_is_one', 'succ_is_new_distinction', 'positive_nat_is_distinction_count', 'primality_summary']);

function open(name) {
  const p = path.join(__dirname, name + '.json');
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  const fix = (prefix, th, fields) => {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
    if (!hit.length) return;                                   // уже внесено
    if (hit.length !== 1) throw new Error(name + ': не одна запись: ' + prefix);
    Object.assign(hit[0], { verdict: 'ok' }, fields); n++;
  };
  const add = (rec) => {
    if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
    j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
  };
  const witness = () => {
    for (const r of j.records) {
      if (!EIGHT.has(r.theorem || '')) continue;
      if (!/classic/.test(r.note || '') || (r.note || '').includes('[13.11, Часть II, шаг 1: свидетель')) continue;
      r.note += WIT; n++;
    }
  };
  const save = () => { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + '.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); };
  return { j, fix, add, witness, save };
}

// ---------------------------------------------------------------- II.1
{
  const { fix, add, witness, save } = open('part02-ch01');
  // § 1.3.3: исключение нуля
  fix('Граничный статус нуля имеет точное формальное следствие', 'zero_not_a_count', {
    note: DONE + ': слово «следствие» стало верным. Исключение нуля получено теоремой, без условия на число: zero_from_absence (счёт нуль — в точности у пустого списка) и zero_is_not_a_presented_count (' + CP + '), обе ' + CL + '. Прежде оно было только условием (1 <= n) в определении distinction_count_from_one.' });
  const CZ = 'То же получено и следствием, без условия на число (файл `CountingPresence.v`): счёт нуль — в точности у пустого списка (`zero_from_absence`), а в пустом списке не предъявлено ни одного акта; поэтому нуль не есть счёт предъявленного (`zero_is_not_a_presented_count`).';
  add({ theorem: 'zero_from_absence', file: CP, claim: CZ, note: 'zero_from_absence : forall Ds : list Distinction, counts Ds 0 <-> Ds = []. ' + CL + '.' });
  add({ theorem: 'zero_is_not_a_presented_count', file: CP, claim: CZ, note: 'zero_is_not_a_presented_count : ~ exists Ds, counts_from_one Ds 0. ' + CL + '.' });
  fix('А `first_count _is_one` показывает', 'first_count_is_one', {
    claim: 'А `first_count_is_one` показывает, с чего он начинается: первый счёт есть единица, и ему отвечает список из одного различия.',
    note: DONE + ': имя, разорванное переносом строки, набрано целиком. Theorem first_count_is_one : distinction_count_from_one 1; свидетель с 13.11 — [distinction_true_false]; ' + CL + '.' });
  // «Зачем два предиката»
  fix('`distinction_count` отвечает на вопрос *технический*: какова длина данного списка различий?', 'distinction_count', {
    claim: '`distinction_count` отвечает на вопрос *технический*: есть ли список различий данной длины?',
    note: DONE + ': было «какова длина данного списка различий?». distinction_count (n : nat) : Prop := exists Ds, length Ds = n — свойство числа: есть ли список такой длины.' });
  add({ theorem: 'distinction_count_of_every_number', file: CP,
    claim: 'поэтому ответ положителен при всяком числе, включая нуль (`distinction_count_of_every_number`).',
    note: 'distinction_count_of_every_number : forall n, distinction_count n. ' + CL + ' (свидетель — список копий distinction_true_false).' });
  fix('Этот предикат нужен везде, где речь идёт о списках как таковых', 'distinction_count', {
    theorem: 'distinction_count_nat', file: F + 'IndivisibleDistinction.v',
    claim: 'Этот предикат говорит о списках как таковых; длину *данного* списка и её поведение при конкатенации в репозитории даёт функция `distinction_count_nat` (файл `IndivisibleDistinction.v`).',
    note: DONE + ': было «нужен везде, где речь идёт… о длинах, индексах, конкатенациях». distinction_count_nat (Ds : list Distinction) : nat := length Ds; count_is_natural (длина конкатенации), distinction_increment — ' + CL + '.' });
  fix('`distinction_count_from_one` отвечает на вопрос *онтологический*: сколько актов различения', 'distinction_count_from_one', {
    claim: '`distinction_count_from_one` отвечает на вопрос *онтологический*: может ли данное число быть счётом *совершённых* актов различения?',
    note: DONE + ': было «сколько актов различения совершено?». Предикат — свойство числа, равносильное 1 <= n (count_from_one_iff_positive, ' + CP + ').' });
  add({ theorem: 'counts_from_one', file: CP,
    claim: 'На вопрос же, сколько актов совершено в *данном* списке, отвечает отношение `counts_from_one` между списком и числом (файл `CountingPresence.v`)',
    note: 'counts_from_one (Ds : list Distinction) (n : nat) : Prop := presented Ds /\\ counts Ds n. У данного списка счёт один (counts_functional).' });
  add({ theorem: 'from_one_iff_some_present_list', file: CP,
    claim: 'предикат говорит, что такой счёт есть у некоторого списка с хотя бы одним предъявленным актом (`from_one_iff_some_present_list`).',
    note: 'from_one_iff_some_present_list : forall n, distinction_count_from_one n <-> exists Ds, counts_from_one Ds n. ' + CL + '.' });
  // «Согласие с предикатом счёта»
  fix('Этот предикат говорит: число $n$ *есть* в системе постольку, поскольку существует список из $n$ совершённых различий.', 'distinction_count_from_one', {
    claim: 'Этот предикат говорит: число $n$ *есть* в системе постольку, поскольку существует список из $n$ совершённых различий и ' + GE + '.',
    note: DONE + ': добавлено второе условие определения. distinction_count_from_one n := exists Ds, length Ds = n /\\ 1 <= n.' });
  fix('Он не описывает накопления от нуля — он регистрирует *наличие* совершённых актов и их число.', 'distinction_count_from_one', {
    theorem: 'count_from_one_iff_positive', file: CP,
    claim: 'Он не описывает накопления от нуля; формально он равносилен условию ' + GE + ' (`count_from_one_iff_positive`) и выражает одно — границу: счёт наличного начинается с единицы.',
    note: DONE + ': было «он регистрирует наличие совершённых актов и их число». count_from_one_iff_positive : forall n, distinction_count_from_one n <-> 1 <= n. ' + CL + '.' });
  add({ theorem: 'counts_from_one', file: CP,
    claim: '*Наличие* совершённых актов и их число регистрирует отношение `counts_from_one` между списком совершённых различений и числом (файл `CountingPresence.v`).',
    note: 'Отношение между ДАННЫМ списком и числом; every_list_has_exactly_one_count, counts_functional — ' + CL + '.' });
  add({ theorem: 'presence_starts_at_one', file: CP,
    claim: 'и из наличия хотя бы одного акта следует ' + GE + ' (`presence_starts_at_one`).',
    note: 'presence_starts_at_one : forall Ds n, counts_from_one Ds n -> 1 <= n. ' + CL + '.' });
  fix('Картина присутствия — словесное выражение того, что предикат `distinction_count_from_one` выражает формально.', 'distinction_count_from_one', {
    theorem: 'counts_from_one', file: CP,
    claim: 'Картина присутствия — словесное выражение того, что отношение `counts_from_one` выражает формально.',
    note: DONE + ': было «предикат distinction_count_from_one». Фиксацию наличного выражает отношение между данным списком и числом.' });
  // разбор E/R/R: имена шапки
  fix('первый акт различения отмечается единицей (`one_is_first`)', 'one_is_first', { file: CP,
    note: DONE + ' (формализацией): one_is_first : forall D : Distinction, counts_from_one [D] 1 /\\ (forall n, counts_from_one [D] n -> n = 1). ' + CL + '. Прежде имя стояло только в шапке PrimalityOfOne.v.' });
  fix('всякое следующее различение даёт следующее число (`succ_from_distinction`)', 'succ_from_distinction', { file: CP,
    note: DONE + ' (формализацией): succ_from_distinction : forall Ds (D : Distinction) n, counts Ds n -> counts_from_one (add_distinction Ds D) (S n). Различение произвольно. ' + CL + '.' });
  fix('нуль — из отсутствия различения (`zero_from_absence`), а не из счёта.', 'zero_from_absence', { file: CP,
    note: DONE + ' (формализацией): zero_from_absence : forall Ds : list Distinction, counts Ds 0 <-> Ds = []. ' + CL + '.' });
  fix('Элементы — сами акты различения, которые счёт и пересчитывает (`ToS_nat`', 'ToS_nat', { file: CP,
    note: DONE + ' (формализацией; развилка — А): ToS_nat : Type := { Ds : list Distinction | presented Ds } — список, в котором предъявлен хотя бы один акт; tos_count_range : (exists c, tos_count c = n) <-> 1 <= n. ' + CL + '. Тип nat не переопределяется.' });
  fix('| акты различения (`ToS_nat`) |', 'ToS_nat', { file: CP, note: DONE + ' (формализацией): то же определение ToS_nat (' + CP + ').' });
  // сноска 15
  fix('E/R/R-разметка в шапке файла `PrimalityOfOne.v`; асимметрия «единица прежде нуля»', null, {
    claim: 'E/R/R-разметка в шапке файла `PrimalityOfOne.v`; три правила шапки доказаны теоремами о данном списке различений — `one_is_first`, `zero_from_absence`, `succ_from_distinction` (файл `CountingPresence.v`; там же определён `ToS_nat` — список, в котором предъявлен хотя бы один акт различения);',
    note: DONE + ': названо, где объявлены три правила шапки и ToS_nat.' });
  fix('E/R/R-разметка в шапке файла `PrimalityOfOne.v`; асимметрия «единица прежде нуля»', 'one_precedes_zero_in_distinction', {
    claim: 'асимметрия «единица прежде нуля» — в `AsymmetricDistinction.v`.' });
  witness();
  save();
}
// ---------------------------------------------------------------- II.2 (только замена свидетеля)
{
  const { j, fix, witness, save } = open('part02-ch02');
  fix('В формальных доказательствах списки различий строятся из *одного и того же* канонического элемента: `first_count_is_one` предъявляет `[distinction_of True]`', 'succ_is_new_distinction', {
    claim: 'В формальных доказательствах списки различий строятся из *одного и того же* канонического элемента: `first_count_is_one` предъявляет `[distinction_true_false]`, а `succ_is_new_distinction` присоединяет `distinction_true_false` к уже имеющемуся списку.',
    note: DONE + ' (развилка «свидетель» — А): в исходнике свидетель заменён на distinction_true_false (PrimalityOfOne.v), теоремы — ' + CL + '.' });
  // два упоминания, ещё не поправленные на странице (ждут показа автору)
  for (const r of j.records) {
    if (/\[distinction_of True\]/.test(r.claim || '') && !/страница отстала/.test(r.note || '')) {
      r.verdict = 'mismatch-statement';
      r.note = 'страница отстала (13.11): в исходнике свидетель заменён на distinction_true_false (слово автора «А»); это упоминание найдено при внесении и ждёт показа автору. Прежняя заметка: ' + (r.note || '');
    }
  }
  witness();
  save();
}
