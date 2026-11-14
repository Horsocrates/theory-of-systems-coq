// Часть III, шаг 1, страницы (2026-11-14, слово автора «Вноси»): 8 правок главы III.1 внесены.
// Формализация — новый src/CoordinateIntegersLaws.v; CoordinateIntegers.v не менялся.
// Запуск: node patch-p03-step-01-pages.cjs  (затем relocate + merge по part03-ch01). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 14.11 (Часть III, шаг 1, слово автора)';
const CL = 'Closed under the global context';
const CI = 'src/CoordinateIntegers.v';
const LW = 'src/CoordinateIntegersLaws.v';
const F = 'src/foundation/';
const BS = String.fromCharCode(92);
const AND = '/' + BS;
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

const p = path.join(__dirname, 'part03-ch01.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
const fix = (prefix, th, fields) => {
  const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
  if (!hit.length) return;
  if (hit.length !== 1) throw new Error('не одна запись: ' + prefix + ' / ' + th);
  Object.assign(hit[0], { verdict: 'ok' }, fields); n++;
};
const add = (rec) => {
  if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
  j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
};

// --- место 1.4: Distinction введена в Части I
const C_D = 'в `Distinction` из Части I оно задано полем `negative` наравне с `positive`, как одна из двух сторон полного различения (Глава I.2).';
fix('в `Distinction` из Части II оно задано полем `negative`', 'Distinction', { claim: C_D,
  note: DONE + ': номер части и главы. Запись Distinction введена в Главе I.2 (Record, foundation/Distinction.v:71).' });
fix('в `Distinction` из Части II оно задано полем `negative`', 'negative', { claim: C_D,
  note: 'Поля positive и negative (Distinction.v:72–73) — две стороны записи; negative D <-> ~ positive D — negative_iff_not_positive (' + F + 'DistinctionCoDefinition.v), ' + CL + '.' });
// --- опора (дополнение)
const C_A = 'Формально это записано так (файл `CoordinateIntegersLaws.v`): пара читается как точка ряда, взятая от опоры (`position_from`); знак позиции задаётся положением точки относительно опоры (`position_sign`), перенос опоры на шаг сдвигает всю разметку на единицу (`anchor_shift`), и одна и та же точка положительна от одной опоры и отрицательна от другой (`same_point_both_signs`).';
add({ theorem: 'position_from', file: LW, claim: C_A, note: 'Definition position_from (k n : nat) : FormalDiff := mkFD n k — точка n, прочитанная от опоры k.' });
add({ theorem: 'position_sign', file: LW, claim: C_A,
  note: 'position_sign : (fd_to_Z (position_from k n) > 0 <-> k < n) ' + AND + ' (… = 0 <-> n = k) ' + AND + ' (… < 0 <-> n < k). ' + CL + '.' });
add({ theorem: 'anchor_shift', file: LW, claim: C_A,
  note: 'anchor_shift : fd_to_Z (position_from (S k) n) = fd_to_Z (position_from k n) - 1. ' + CL + '.' });
add({ theorem: 'same_point_both_signs', file: LW, claim: C_A,
  note: 'same_point_both_signs : fd_to_Z (position_from 0 (S n)) > 0 ' + AND + ' fd_to_Z (position_from (S (S n)) (S n)) < 0. ' + CL + '.' });
// --- место 1.3: «один и тот же тип»
fix('Обе конструкции — через три конструктора и через классы пар — равнозначны: задают один и тот же тип', 'fd_equiv_iff_Z', {
  theorem: 'FormalDiff_iso_Z', file: LW,
  claim: 'Обе конструкции — через три конструктора и через классы пар — равнозначны: задают одни и те же целые числа — классы пар взаимно однозначно отвечают значениям типа `Z`, и сложение, умножение, смена знака и порядок при этом сохраняются (теорема `FormalDiff_iso_Z`, файл `CoordinateIntegersLaws.v`);',
  note: DONE + ' (формализацией и словами): было «один и тот же тип». Типов два (Z и FormalDiff с fd_equiv; fd_of_to_Z_not_eq, fd_to_Z_not_injective); соответствие по классам пар в полном виде — FormalDiff_iso_Z (девять конъюнктов: оба обхода, сложение, умножение, смена знака, нуль, единица, порядок). ' + CL + '.' });
add({ theorem: 'unique_reduced_in_class', file: LW,
  claim: 'в каждом классе пар ровно одна приведённая — с шагами по одну сторону (`unique_reduced_in_class`).',
  note: 'unique_reduced_in_class : forall x, exists r, (fd_reduced r ' + AND + ' fd_equiv r x) ' + AND + ' (forall r\', fd_reduced r\' ' + AND + ' fd_equiv r\' x -> r\' = r). ' + CL + '.' });
// --- § 1.7: формальная опора вывода правила знаков (дополнение)
const C_S = 'Этот вывод проведён и формально (файл `CoordinateIntegersLaws.v`): умножение задано повторением смещения (`fd_mul_rep`), разворот любого из множителей разворачивает результат (`fd_mul_rep_opp_l`, `fd_mul_rep_opp_r`), и правило знаков получено из двух разворотов — теорема `fd_sign_rule_from_two_flips`.';
add({ theorem: 'fd_sign_rule_from_two_flips', file: LW, claim: C_S,
  note: 'fd_sign_rule_from_two_flips : forall x y, fd_mul_rep (fd_opp x) (fd_opp y) = fd_mul_rep x y. Доказательство: fd_mul_rep_opp_l, fd_mul_rep_opp_r, fd_opp_involutive; формула умножения не раскрывается, к Z обращения нет. ' + CL + '.' });
add({ theorem: 'fd_mul_rep', file: LW, claim: C_S,
  note: 'Definition fd_mul_rep x y := fd_add (fd_rep x (fd_pos y)) (fd_rep (fd_opp x) (fd_neg y)) — повторить прямо fd_pos y раз и с разворотом fd_neg y раз. Чтение взято из § 1.7 главы; это определение, не вывод (шапка файла говорит это).' });
add({ theorem: 'fd_mul_rep_opp_l', file: LW, claim: C_S, note: 'fd_mul_rep_opp_l : fd_mul_rep (fd_opp x) y = fd_opp (fd_mul_rep x y). ' + CL + '.' });
add({ theorem: 'fd_mul_rep_opp_r', file: LW, claim: C_S, note: 'fd_mul_rep_opp_r : fd_mul_rep x (fd_opp y) = fd_opp (fd_mul_rep x y). ' + CL + '.' });
// --- место 1.2: файлы Части II
fix('Главы Части II опирались на собственные файлы Rocq-репозитория ToS', 'one_from_distinction', {
  claim: 'Главы Части II опирались на собственные файлы Rocq-репозитория ToS — `Distinction.v`, `PrimalityOfOne.v`, `Binarity.v` и другие, — в которых чтение натурального ряда от акта различения записано и машинно проверено над стандартным типом `nat`.',
  note: DONE + ': было «натуральный ряд и его устройство выведены и доказаны». Тип nat берётся готовым; чтение записано и проверено (после аудита Части II — без допущений: CountingPresence.v, FourPathsOneSeries.v). Согласовано со словами Главы II.1.' });
// --- сноска 1
fix('Тип `Z` целых чисел определён в стандартной библиотеке Rocq — в модуле `ZArith`.', 'ZArith', {
  claim: 'Тип `Z` целых чисел принадлежит библиотеке самого Rocq: объявлен он в модуле `BinNums`, арифметика над ним — модуль `ZArith`.',
  note: DONE + ': Locate Z — Inductive Corelib.Numbers.BinNums.Z; ZArith даёт арифметику и вывозит имя.' });
// --- место 1.1: сноска 2
fix('а правило знаков $(-a)(-b)=ab$ — как теорему о `FormalDiff` (13 лемм, 0 аксиом).', 'fd_sign_rule', {
  page_price: '0 аксиом',
  note: DONE + ' (формализацией): слова остаются; к ним добавлено, что формула fd_mul правило уже содержит, а вывод из двух разворотов дан в CoordinateIntegersLaws.v. fd_sign_rule (CoordinateIntegers.v:127); в файле 13 Qed; ' + CL + '.' });
add({ theorem: 'fd_mul', file: CI,
  claim: 'Умножение пар задано там формулой, которая правило уже содержит.',
  note: 'Верно: fd_mul x y := mkFD (pos x * pos y + neg x * neg y) (pos x * neg y + neg x * pos y) — произведение двух минус-счётов стоит в плюс-стороне по определению (fd_mul_neg_neg_by_definition, ' + LW + ').' });
add({ theorem: 'fd_mul_rep_eq', file: LW,
  claim: 'В файле `CoordinateIntegersLaws.v` (тоже без аксиом) умножение задано так, как его вводит § 1.7, — повторением смещения (`fd_mul_rep`); оно совпадает с формулой первого файла (`fd_mul_rep_eq`), а правило знаков получено из того, что двойной разворот есть тождество (`fd_sign_rule_from_two_flips`).',
  page_price: 'без аксиом',
  note: 'fd_mul_rep_eq : forall x y, fd_mul_rep x y = fd_mul x y (равенство пар). В файле 35 Qed; у всех объявлений Print Assumptions — ' + CL + '.' });
fix('Стандартный `Z` остаётся *целью* изоморфизма; своя координатная конструкция теперь машинно построена над ним.', 'fd_to_of_Z', {
  claim: 'Стандартный `Z` остаётся *целью* изоморфизма; своя координатная конструкция машинно построена над счётами типа `nat`, с отображением в `Z`.',
  note: DONE + ': было «построена над ним». Record FormalDiff — два поля типа nat; Z — область значений fd_to_Z.' });

fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part03-ch01.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
