// Часть III, шаг 2, страницы (2026-11-14, слово автора «Вноси; А»): 6 правок главы III.2 и оговорка о статусе
// в варианте А (запись Commens оставлена и названа) внесены. Формализация — новый src/CommensurationQ.v.
// Место 2.3 (биекция) закрывается шагом 3.
// Запуск: node patch-p03-step-02-pages.cjs  (затем relocate + merge по part03-ch02). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 14.11 (Часть III, шаг 2, слово автора)';
const CL = 'Closed under the global context';
const CQ = 'src/CommensurationQ.v';
const BS = String.fromCharCode(92);
const AND = '/' + BS;
const NEQ = '$q ' + BS + 'neq 0$';
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

const p = path.join(__dirname, 'part03-ch02.json');
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

// --- позиционное чтение (дополнение)
const C_POS = '$p/q$ есть $p$-кратное повторение малого шага $1/q$ (`position_is_multiple_of_small_step`; $q$ малых шагов составляют единицу — `small_steps_make_unit`; файл `CommensurationQ.v`).';
add({ theorem: 'position_is_multiple_of_small_step', file: CQ, claim: C_POS,
  note: 'position_is_multiple_of_small_step : forall (p : Z) (q : positive), p # q == inject_Z p * (1 # q). ' + CL + '.' });
add({ theorem: 'small_steps_make_unit', file: CQ, claim: C_POS,
  note: 'small_steps_make_unit : forall q : positive, inject_Z (Z.pos q) * (1 # q) == 1. ' + CL + '.' });
// --- § 2.4 (дополнение)
const C_EQ = 'Формально (файл `CommensurationQ.v`): при $q = 0$ и $p ' + BS + 'neq 0$ шага нет (`zero_parts_no_step`), при $q = 0$ и $p = 0$ годится всякий (`zero_parts_any_step`), и уравнение задаёт шаг — решение есть и оно одно — в точности при ' + NEQ + ' (`commensuration_determines_iff`).';
add({ theorem: 'zero_parts_no_step', file: CQ, claim: C_EQ, note: 'zero_parts_no_step : forall p u : Q, ~ p == 0 -> ~ (0 * u == p). ' + CL + '.' });
add({ theorem: 'zero_parts_any_step', file: CQ, claim: C_EQ, note: 'zero_parts_any_step : forall u : Q, 0 * u == 0. ' + CL + '.' });
add({ theorem: 'commensuration_determines_iff', file: CQ, claim: C_EQ,
  note: 'commensuration_determines_iff : forall q p : Q, determines_step q p <-> ~ q == 0, где determines_step q p := exists u, q * u == p ' + AND + ' forall u\', q * u\' == p -> u\' == u. ' + CL + '.' });
// --- место 2.1
fix('Тем условие ' + NEQ + ' (§ 2.4) оказывается *встроенным в самый тип*', 'Qinv', {
  claim: 'Тем условие ' + NEQ + ' (§ 2.4) оказывается *встроенным в самый тип*: знаменатель просто не может быть нулём, и дроби с нулевым знаменателем формальная запись не допускает не запретом, а устройством типа.',
  note: DONE + ': было «деления на нуль формальная запись не допускает». Типом исключена дробь с нулевым знаменателем (denominator_never_zero, ' + CQ + '); об операции деления страница теперь говорит отдельно.' });
add({ theorem: 'Qinv', external: true, assumptions: CL,
  claim: 'Об *операции* деления нужна оговорка: библиотечная функция деления определена для любой пары чисел и при нулевом делителе возвращает нуль — техническое соглашение, принятое, чтобы функция была определена всюду; закон обратного элемента библиотека доказывает при условии $x ' + BS + 'neq 0$.',
  verdict: 'ok', note: 'Верно: Qinv 0 = 0 (QArith_base.v:254), Qdiv x y := x * / y; Qmult_inv_r : ~ x == 0 -> x * / x == 1. В ' + CQ + ': Qinv_of_zero, Qdiv_by_zero (x / 0 == 0), inverse_law_fails_at_zero — ' + CL + '.' });
add({ theorem: 'library_value_at_zero_is_not_a_solution', file: CQ,
  claim: 'Уравнения соразмерности это соглашение не решает (§ 2.4; теорема `library_value_at_zero_is_not_a_solution`, файл `CommensurationQ.v`).',
  note: 'library_value_at_zero_is_not_a_solution : forall p : Q, ~ p == 0 -> ~ (0 * (p / 0) == p). ' + CL + '.' });
fix('Ненулевость знаменателя встроена в тип: деления на нуль формальная запись не допускает', 'Qinv', {
  claim: 'Ненулевость знаменателя встроена в тип: дроби с нулевым знаменателем формальная запись не допускает устройством, а не запретом; операция деления в библиотеке определена всюду и при нулевом делителе возвращает нуль по техническому соглашению.',
  note: DONE + ': то же уточнение в итоге раздела. Qdiv_by_zero : forall x, x / 0 == 0 (' + CQ + '), ' + CL + '.' });
// --- медианта (дополнение)
add({ theorem: 'mediant_between_Q', file: CQ,
  claim: 'новая соразмерная позиция, полученная из двух данных (`mediant_between_Q`, файл `CommensurationQ.v`).',
  note: 'mediant_between_Q : forall (a c : Z) (b d : positive), a # b < c # d -> a # b < (a + c) # (b + d) ' + AND + ' (a + c) # (b + d) < c # d. ' + CL + '.' });
// --- место 2.2: оговорка о статусе (развилка — А)
fix('Оговорка о статусе, как и для целых (Глава III.1): ToS не строит свой тип рациональных', 'FormalDiff', {
  theorem: 'Commens', file: CQ,
  claim: 'Соразмерное чтение, как и у целых (Глава III.1), имеет теперь свой файл-якорь — `CommensurationQ.v`: уравнение соразмерности задаёт шаг в точности при ' + NEQ + ' (`commensuration_determines_iff`), позиция $p/q$ есть малый шаг $1/q$, взятый $p$ раз (`position_is_multiple_of_small_step`), и дана запись соразмерной позиции `Commens` — число взятых шагов и число новых границ внутри единичного шага, — взаимно однозначно отвечающая `Q` (`cm_to_of`, `cm_of_to`);',
  note: DONE + ' (формализацией; развилка — А): было «как и для целых: ToS не строит свой тип». Record Commens := mkCm { cm_steps : Z ; cm_cuts : nat }; cm_to_of : cm_to_Q (cm_of_Q q) = q; cm_of_to : cm_of_Q (cm_to_Q x) = x; cm_eq_iff_Qeq, cm_add_to_Q, cm_mul_to_Q — ' + CL + '.' });
add({ theorem: 'cm_to_of', file: CQ, claim: '(`cm_to_of`, `cm_of_to`); это та же пара, прочитанная по границам, а не по частям.',
  note: 'Верно и названо на странице прямо: Commens — пара Q с числом границ вместо числа частей (cm_parts x = cm_cuts x + 1); содержание несут теоремы.' });
add({ theorem: 'cm_of_to', file: CQ, claim: '(`cm_to_of`, `cm_of_to`); это та же пара, прочитанная по границам, а не по частям.',
  note: 'cm_of_to : forall x : Commens, cm_of_Q (cm_to_Q x) = x. ' + CL + '.' });
const C_ST = 'Оговорка о статусе: рабочий тип рациональных ToS не строит — пользуется стандартным `Q` из `QArith` (`Record` числитель/знаменатель, § 2.5); машинно проверены полевая арифметика `Q` и отношение `Qeq`.';
fix('машинно проверенное — сама полевая арифметика `Q` и отношение `Qeq`, а соразмерное чтение несёт проза.', 'Qsft', { claim: C_ST,
  note: 'В библиотеке: Qsft : field_theory … Qeq (Stdlib/QArith/Qfield.v:31), Qmult_inv_r, Q_Setoid : Equivalence Qeq. Рабочий тип — стандартный Q; это верно.' });
fix('машинно проверенное — сама полевая арифметика `Q` и отношение `Qeq`, а соразмерное чтение несёт проза.', 'Q_field', { claim: C_ST,
  note: 'В проекте законы поля для Q собраны записью Q_field : Field (stdlib/RingField.v:314); ' + CL + '.' });
fix('Файл `Countability_Q.v` (дерево Калкина–Уилфа) есть якорь *следующей* главы и работает', 'QPos', {
  claim: 'Файл `Countability_Q.v` (дерево Калкина–Уилфа) есть якорь *следующей* главы: он работает с *положительными* парами `QPos` и достраивает обход до всего $ℚ$ (§ 2.8.5).',
  note: DONE + ': описание файла дополнено. QPos := (positive * positive)%type (Countability_Q.v:42); разделы со стр. 534 — enum_Q, Q_countable, index_of_Q, Q_bijection для всего Q.' });
// --- сноска 1
fix('Тип `Q` рациональных чисел определён в стандартной библиотеке Rocq — в модуле `QArith`.', 'Q', {
  claim: 'Тип `Q` рациональных чисел определён в стандартной библиотеке Rocq — в модуле `QArith`. Как и тип `Z` целых чисел (Глава III.1, § 1.6), он принадлежит библиотеке Rocq, а не Rocq-репозиторию ToS.',
  note: DONE + ': вторая фраза. Объявление — Stdlib.QArith.QArith_base; в репозитории ToS типа Q нет.' });

// имя стандартной библиотеки: запись помечается внешней (повторный запуск правит уже добавленную запись)
for (const r of j.records) if (r.theorem === 'Qinv' && !r.external) { r.external = true; r.assumptions = CL; delete r.file; n++; }

fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part03-ch02.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
