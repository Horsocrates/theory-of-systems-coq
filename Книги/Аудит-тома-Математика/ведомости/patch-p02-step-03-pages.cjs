// Часть II, шаг 3, страницы (2026-11-13, слово автора «Вноси; А»): 14 правок главы II.2 и правка-развилка
// (отсылка к Главе I.6 снята) внесены. Формализация — src/foundation/CountingPresence.v (шаг 1) и новый
// src/foundation/CountingStages.v (счёт как процесс стадий, индукция по списку).
// Запуск: node patch-p02-step-03-pages.cjs  (затем relocate + merge по part02-ch02). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть II, шаг 3, слово автора)';
const F = 'src/foundation/';
const CP = F + 'CountingPresence.v';
const CS = F + 'CountingStages.v';
const PO = F + 'PrimalityOfOne.v';
const DI = F + 'Distinction.v';
const EL = 'src/process/ProcessEquivLimit.v';
const CL = 'Closed under the global context';
const BS = String.fromCharCode(92);
const LE = '$1 ' + BS + 'le n$';
const GE = '$n ' + BS + 'ge 1$';
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

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
  const save = () => { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + '.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); };
  return { j, fix, add, save };
}

{
  const { j, fix, add, save } = open('part02-ch02');

  // --- § «Определение distinction_count»
  fix('Предикат `distinction_count` $n$ истинен, если такой список существует, и ложен в противном случае.', 'distinction_count_any', {
    claim: 'Предикат `distinction_count` $n$ истинен, если такой список существует. Существует он для всякого $n$ — лемма `distinction_count_any` того же файла, без допущений; предикат, стало быть, выполнен для каждого натурального числа, включая нуль.',
    page_price: 'без допущений',
    note: DONE + ': было «и ложен в противном случае». Lemma distinction_count_any : forall n, distinction_count n (Distinction.v). С 13.11 (замена свидетеля) — ' + CL + '.' });
  fix('`distinction_count` — именно предикат: характеристика, которой число либо обладает, либо нет.', 'distinction_count', {
    claim: '`distinction_count` — именно предикат: высказывание о числе, а не определение числа; и высказывание это, как сказано, верно о всяком числе.',
    note: DONE + ': было «характеристика, которой число либо обладает, либо нет». Definition distinction_count (n : nat) : Prop := exists Ds, length Ds = n; верно для всякого n (distinction_count_any).' });
  // --- § «Технический слой»
  add({ theorem: 'distinction_count_any', file: DI,
    claim: 'Ответ формализации: достижим всякий итог — для каждого $n$, включая нуль, список нужной длины существует (`distinction_count_any`).',
    note: 'distinction_count_any : forall n, distinction_count n. ' + CL + '.' });
  add({ theorem: 'distinction_count', file: DI,
    claim: 'Сказанное помещает `distinction_count` на вполне определённое место — в *технический слой* формальной работы.',
    note: DONE + ' (развилка — А): отсылка к Главе I.6 снята. Там техническим слоем названы два объявления платформы (classic, L4_witness); distinction_count — определение. Слово «технический» здесь — в смысле главы: запись о форме данных.' });
  // --- § «Список различий и длина как акт подсчёта»
  add({ theorem: 'length_is_the_count', file: CS,
    claim: 'Такой подсчёт один: всякая функция, дающая нуль на пустом списке и прибавляющая единицу на каждом встреченном различии, совпадает с `length` (`length_is_the_count`, файл `CountingStages.v`).',
    note: 'length_is_the_count : forall (A : Type) (f : list A -> nat), f [] = 0 -> (forall a l, f (a :: l) = S (f l)) -> forall l, f l = length l. ' + CL + '. Для списков различений и add_distinction — counting_of_acts_is_unique.' });
  // --- § «Нуль выпадает, единица входит»
  fix('То, что в § 1.3 было онтологическим положением, здесь стало доказанной парой теорем.', 'zero_not_a_count', {
    note: DONE + ' (формализацией и оговоркой): слова «доказанной парой теорем» получили опору. В самом предикате границу проводит условие 1 <= n определения (zero_not_a_count его возвращает); выводом, без условия на число, исключение нуля дают zero_is_not_a_presented_count и from_one_iff_some_present_list (' + CP + '), обе ' + CL + '.' });
  add({ theorem: 'zero_not_a_count', file: PO,
    claim: 'Оговорка о первой из них: в самом предикате границу проводит условие ' + LE + ', вписанное в определение, и `zero_not_a_count` это условие возвращает.',
    note: 'Верно: zero_not_a_count : ~ distinction_count_from_one 0; доказательство отбрасывает список и берёт конъюнкт 1 <= 0 (intro H. destruct H as [_ [_ Hge]]. lia). ' + CL + '.' });
  add({ theorem: 'zero_is_not_a_presented_count', file: CP,
    claim: 'Выводом, без условия на число, исключение нуля получено отдельно (файл `CountingPresence.v`): в списке, где предъявлен хотя бы один акт, счёт не нуль (`zero_is_not_a_presented_count`)',
    note: 'zero_is_not_a_presented_count : ~ exists Ds, counts_from_one Ds 0. ' + CL + '.' });
  add({ theorem: 'from_one_iff_some_present_list', file: CP,
    claim: 'и такие счёты — в точности числа, удовлетворяющие предикату (`from_one_iff_some_present_list`).',
    note: 'from_one_iff_some_present_list : forall n, distinction_count_from_one n <-> exists Ds, counts_from_one Ds n. ' + CL + '.' });
  // --- § «Шаг наращивания»
  fix('Если же где-то понадобится хронологическое чтение слева направо, его даёт альтернативная операция присоединения в конец списка (`snoc`)', 'snoc', {
    theorem: 'snoc_distinction', file: CP,
    claim: 'Если же где-то понадобится хронологическое чтение слева направо, его даёт альтернативная операция присоединения в конец списка (`snoc_distinction`, файл `CountingPresence.v`);',
    note: DONE + ' (формализацией): было имя `snoc`, которого нет. Definition snoc_distinction (Ds : list Distinction) (D : Distinction) : list Distinction := Ds ++ [D]; snoc_distinction_increments, snoc_is_reversed_add — ' + CL + '.' });
  add({ theorem: 'add_and_snoc_same_count', file: CP,
    claim: 'счёт при ней тот же (`add_and_snoc_same_count`), и кардинальный путь настоящей главы в ней не нуждается, поскольку опирается на длину, а не на направление порядка.',
    note: 'add_and_snoc_same_count : forall Ds D n, counts (add_distinction Ds D) n <-> counts (snoc_distinction Ds D) n. ' + CL + '.' });
  fix('Содержательно теорема говорит то, что Глава II.1 назвала бы переходом к следующему числу', 'succ_is_new_distinction', {
    claim: 'Содержательно это доказательство проводит то, что Глава II.1 назвала бы переходом к следующему числу: *следующее число есть нынешнее плюс ещё один совершённый акт*. Само утверждение теоремы говорит только, что список длины $n + 1$ существует;',
    note: DONE + ': было «содержательно теорема говорит». Верно: утверждение succ_is_new_distinction — существование списка длины S n; присоединение акта — ход доказательства (exists (distinction_true_false :: Ds)). ' + CL + '.' });
  add({ theorem: 'succ_count_iff_one_more_act', file: CP,
    claim: 'связь двух списков удерживает теорема `succ_count_iff_one_more_act` (файл `CountingPresence.v`): список имеет счёт $n + 1$ в точности тогда, когда он получен присоединением одного различия к списку со счётом $n$.',
    note: 'succ_count_iff_one_more_act : forall (n : nat) (Ds : list Distinction), counts Ds (S n) <-> exists D Ds\', Ds = add_distinction Ds\' D /' + BS + ' counts Ds\' n. ' + CL + '.' });
  // --- § «От единицы ко всякому числу»: разорванное имя
  fix('ToS устанавливает соединение теоремой `positive_nat_is_distinction` _`count`', 'positive_nat_is_distinction', {
    theorem: 'positive_nat_is_distinction_count', file: PO,
    claim: 'ToS устанавливает соединение теоремой `positive_nat_is_distinction_count`; её доказательство устроено так.',
    note: DONE + ': имя, разорванное переносом строки, набрано целиком. Theorem positive_nat_is_distinction_count : forall n, (1 <= n)%nat -> distinction_count_from_one n; с 13.11 — ' + CL + '.' });
  {
    // вторая запись того же места (осколок count) больше не нужна: такого имени на странице нет
    const k = j.records.findIndex((r) => r.theorem === 'count' && norm(r.claim).startsWith('ToS устанавливает соединение теоремой'));
    if (k >= 0) { j.records.splice(k, 1); console.log('запись об осколке имени снята'); }
  }
  // --- § «Индукция есть форма повторимого акта»
  add({ theorem: 'count_induction_along_list', file: CS,
    claim: 'Один шаг навстречу в формальном слое сделан (файл `CountingStages.v`): теорема `count_induction_along_list` — база для счёта одного акта и шаг на ещё один акт дают свойство для счёта всякого списка, в котором предъявлен хотя бы один акт, — доказана индукцией по самому *списку различий*, без индукции по `nat`.',
    note: 'count_induction_along_list : forall P : nat -> Prop, P 1 -> (forall n, P n -> P (S n)) -> forall Ds : list Distinction, presented Ds -> P (length Ds). ' + CL + '. В терме доказательства (команда Print, _p02step3/Verify.out) из принципов индукции только list_ind; nat_ind не входит.' });
  add({ theorem: 'positive_nat_is_distinction_count', file: PO,
    claim: 'Полной замены это не даёт: индукция по списку приходит вместе с типом списков, а что список есть у всякого ' + GE + ', доказано индукцией по `nat`.',
    note: 'Верно: positive_nat_is_distinction_count доказана тактикой induction n (nat_ind); list_ind порождён определением типа list. Страница называет границу прямо.' });
  // --- § «Бесконечность как возможность…: P4»
  add({ theorem: 'present_at_iff', file: CS,
    claim: 'Обе стороны проверены вместе (файл `CountingStages.v`): на стадии, заданной списком различий, наличны в точности счёты от $1$ до длины списка (`present_at_iff`);',
    note: 'present_at_iff : forall Ds n, present_at Ds n <-> 1 <= n /' + BS + ' n <= length Ds. ' + CL + '.' });
  add({ theorem: 'next_stage_adds_exactly_one', file: CS,
    claim: 'следующая стадия сохраняет наличное и добавляет ровно один новый счёт (`next_stage_adds_exactly_one`);',
    note: 'next_stage_adds_exactly_one : forall Ds D n, present_at (add_distinction Ds D) n <-> present_at Ds n ' + BS + '/ n = S (length Ds). ' + CL + '.' });
  add({ theorem: 'every_number_but_not_all_at_once', file: CS,
    claim: 'всякое ' + GE + ' налично на некоторой стадии, и ни одна стадия не предъявляет всех (`every_number_but_not_all_at_once`).',
    note: 'every_number_but_not_all_at_once : (forall n, 1 <= n -> exists Ds, present_at Ds n) /' + BS + ' (forall Ds, ~ (forall n, 1 <= n -> present_at Ds n)). ' + CL + '.' });
  fix('и из *моста* (`bridge`), переводящего членство в ряду в актуальную предъявленность на конечной стадии.', 'bridge', {
    claim: 'и из *моста* (`bridge`), переводящего членство в ряду в актуальную предъявленность на одной стадии (в записи `bridge` — на нулевой;',
    note: DONE + ': было «на конечной стадии». Definition bridge S actual := forall n, S n -> actual 0 n (P4CompletedInfinity.v:48) — мост ведёт на нулевую стадию.' });
  add({ theorem: 'completed_inf_contradicts_P4_at_any_stage', file: CS,
    claim: 'для любой другой одной стадии противоречие то же — `completed_inf_contradicts_P4_at_any_stage`, файл `CountingStages.v`;',
    note: 'completed_inf_contradicts_P4_at_any_stage : forall M actual s, CompletedInfSet M -> P4_stage_bounded actual -> (forall n, M n -> actual s n) -> False. ' + CL + '.' });
  add({ theorem: 'pointwise_bridge_is_compatible', file: CS,
    claim: 'мост же «каждый член — на своей стадии» с $P4$ совместим — `pointwise_bridge_is_compatible`).',
    note: 'pointwise_bridge_is_compatible : exists M actual, CompletedInfSet M /' + BS + ' P4_stage_bounded actual /' + BS + ' (forall n, M n -> exists stage, actual stage n). ' + CL + '.' });
  // --- § «Что отсюда следует для дальнейшего»
  fix('и отношение `process_equiv` — эквивалентность процессов *по пределу*', 'process_equiv', {
    claim: 'и отношение `process_equiv` — эквивалентность процессов, расхождение которых уходит ниже всякой точности (для процессов с рациональным пределом — *по пределу*), доказанное отношением эквивалентности',
    note: DONE + ': было «эквивалентность процессов по пределу». process_equiv R1 R2 := forall eps > 0, exists N, forall n >= N, Qabs (R1 n - R2 n) < eps (ProcessCore.v:170); сходимости не требует (equiv_does_not_require_convergence); для процессов с рациональным пределом — equiv_iff_same_limit_when_one_converges (' + EL + '). Отношение эквивалентности: process_equiv_refl, _sym, _trans; Instance process_equiv_Equivalence (RealPointSetoid.v:61).' });
  add({ theorem: 'equiv_is_not_pointwise', file: EL,
    claim: 'и не сводящееся к поточечному равенству (`equiv_is_not_pointwise`, файл `ProcessEquivLimit.v`).',
    note: 'equiv_is_not_pointwise : exists R1 R2 : RealProcess, R1 ~~ R2 /' + BS + ' forall n : nat, ~ (R1 n == R2 n). ' + CL + '.' });
  // --- § «Разбор E/R/R»
  fix('добавив доказанные предикаты счёта (§ 2.3–2.4) и потенциальную бесконечность (§ 2.7)', 'distinction_count', {
    claim: 'добавив предикаты счёта (§ 2.3–2.4) и потенциальную бесконечность (§ 2.7), и проверим сформированность.',
    note: DONE + ': слово «доказанные» снято — предикаты суть определения.' });
  fix('формальные предикаты `distinction_count` и `distinction_count_from_one` доказаны', 'distinction_count_from_one', {
    claim: 'формальные предикаты `distinction_count` и `distinction_count_from_one` определены, и теоремы о них доказаны (`Distinction.v`, `PrimalityOfOne.v`, `CountingPresence.v`), но онтологическое чтение несёт проза.',
    note: DONE + ': было «предикаты… доказаны». Оба имени — Definition; теоремы о них — в трёх названных файлах, с 13.11 все без допущений.' });
  // --- сноска 2
  const C_FN2 = 'Предикат `distinction_count_from_one`, операция `add_distinction` и относящиеся к ним теоремы (`first_count_is_one`, `zero_not_a_count`, `add_distinction_increments`, `succ_is_new_distinction`, `positive_nat_is_distinction_count`) находятся в файле `PrimalityOfOne.v` Rocq-репозитория ToS;';
  fix('Предикат `distinction_count_from_one` и относящиеся к нему теоремы (`first_count_is_one`', 'add_distinction', {
    claim: C_FN2,
    note: DONE + ': сноска 2. add_distinction названа операцией (Definition), в перечень теорем поставлена add_distinction_increments.' });
  fix('Предикат `distinction_count_from_one` и относящиеся к нему теоремы (`first_count_is_one`', 'positive_nat_is_distinction_count', {
    claim: C_FN2,
    note: 'Сноска 2. Все названные имена объявлены в src/foundation/PrimalityOfOne.v; файл назван верно.' });
  add({ theorem: 'add_distinction_increments', file: PO, claim: C_FN2,
    note: 'add_distinction_increments : forall Ds D, length (add_distinction Ds D) = S (length Ds). ' + CL + '.' });
  add({ theorem: 'counts_from_one', file: CP,
    claim: 'теоремы о счёте *данного* списка различий — в файле `CountingPresence.v`, о стадиях счёта — в файле `CountingStages.v`.',
    note: 'Верно: CountingPresence.v (30 Qed) — отношения counts, counts_from_one между данным списком и числом; CountingStages.v (22 Qed) — present_at и стадии. Все теоремы обоих файлов — ' + CL + '.' });
  save();
}
