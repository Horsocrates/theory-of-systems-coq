// Часть II, шаг 5, страницы (2026-11-14, слово автора «Делай, А»): 9 правок главы II.4 и правка-развилка
// (А: слово «непустой» в первой формулировке индукции по записям и в её обосновании) внесены.
// Формализация — новый src/foundation/BitStringCount.v; DistinctionSideRole.v (шаг 2). BitString.v не менялся.
// Запуск: node patch-p02-step-05-pages.cjs  (затем relocate + merge по part02-ch04). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 14.11 (Часть II, шаг 5, слово автора)';
const F = 'src/foundation/';
const BC = F + 'BitStringCount.v';
const BSF = F + 'BitString.v';
const BI = F + 'Binarity.v';
const SR = F + 'DistinctionSideRole.v';
const PO = F + 'PrimalityOfOne.v';
const CL = 'Closed under the global context';
const BS = String.fromCharCode(92);
const GE = '$n ' + BS + 'ge 1$';
const OR = BS + '/';
const AND = '/' + BS;
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
  const { fix, add, save } = open('part02-ch04');

  // --- § 4.2: связь Side с записью Distinction
  add({ theorem: 'exactly_one_side_holds', file: SR,
    claim: 'Связь типа `Side` с записью `Distinction` записана отдельно: у всякого различения положена ровно одна из двух сторон типа `Side` — существование даёт исчерпанность ($L3$ записи), единственность — несовместность ($L2$ записи) (`exactly_one_side_holds`, файл `DistinctionSideRole.v`);',
    note: 'exactly_one_side_holds : forall D : Distinction, exists s : DistinctionSide, side_holds D s ' + AND + ' (forall s\', side_holds D s\' -> s\' = s). Существование — из поля exhaustive, единственность — из поля exclusive. ' + CL + '. Тип Side остаётся отдельным объявлением (Binarity.v) — страница говорит это выше.' });
  add({ theorem: 'every_list_has_exactly_one_record', file: BC,
    claim: 'и всякий список совершённых различений имеет ровно одну двоичную запись, той же длины (`every_list_has_exactly_one_record`, файл `BitStringCount.v`).',
    note: 'every_list_has_exactly_one_record : forall Ds : list Distinction, exists bs : BitString, binary_record Ds bs ' + AND + ' bit_length bs = length Ds ' + AND + ' (forall bs\', binary_record Ds bs\' -> bs\' = bs); binary_record Ds bs := Forall2 side_holds Ds bs. ' + CL + '.' });
  // --- § 4.4.3: заготовки моста к физике
  fix('Это — комбинаторные леммы о степенях двойки плюс комментарии', 'microstates', {
    claim: 'Это — арифметические леммы о степенях двойки плюс комментарии, намечающие связь с энтропией;',
    note: DONE + ': было «комбинаторные». Леммы Binarity.v о two_pow (pow_monotone, pow_positive, pow_double, new_dist_doubles и значения) — арифметика функции 2^K; счёта объектов в них нет. Все ' + CL + '.' });
  add({ theorem: 'bitstrings_of_length_count', file: BC,
    claim: 'счёт самих записей дан отдельно (файл `BitStringCount.v`, теорема `bitstrings_of_length_count`): записей длины $K$ ровно $2^K$ — их перечисление полно и без повторов,',
    note: 'bitstrings_of_length_count : forall K, NoDup (all_bitstrings K) ' + AND + ' (forall bs, In bs (all_bitstrings K) <-> bit_length bs = K) ' + AND + ' length (all_bitstrings K) = microstates K. ' + CL + '.' });
  add({ theorem: 'bitstrings_count_is_forced', file: BC,
    claim: 'и всякое другое такое перечисление имеет ту же длину (`bitstrings_count_is_forced`).',
    note: 'bitstrings_count_is_forced : forall K l, NoDup l -> (forall bs, In bs l <-> bit_length bs = K) -> length l = two_pow K. ' + CL + '.' });
  add({ theorem: 'microstates', file: BI,
    claim: 'Полный физический вывод энтропийных законов в них ещё не содержится и относится к физике.',
    note: 'Верно: в Binarity.v и BitStringCount.v об энтропии — только комментарии; теорем нет.' });
  // --- § 4.4: число-сторона
  fix('число-сторона («для всякого ' + GE + ' есть запись длины $n$») читается с него прямо', null, {
    theorem: 'positive_nat_is_bit_count', file: BC,
    claim: 'число-сторона («для всякого ' + GE + ' есть запись длины $n$») доказана отдельно — теоремой `positive_nat_is_bit_count` (файл `BitStringCount.v`)',
    note: DONE + ' (формализацией): было «читается с него прямо». positive_nat_is_bit_count : forall n, 1 <= n -> exists bs : BitString, bs <> [] ' + AND + ' bit_length bs = n. ' + CL + ' (свидетель — запись из n знаков Marked).' });
  add({ theorem: 'bit_count_iff_positive', file: BC,
    claim: 'а вместе с обратным направлением — `bit_count_iff_positive`: длины непустых записей суть в точности числа ' + GE + '.',
    note: 'bit_count_iff_positive : forall n, (exists bs : BitString, bs <> [] ' + AND + ' bit_length bs = n) <-> 1 <= n. ' + CL + '.' });
  fix('число-сторона («для всякого ' + GE + ' есть запись длины $n$») читается с него прямо', 'positive_nat_is_distinction_count', {
    claim: 'Она параллельна уже доказанной `positive_nat_is_distinction_count` из `PrimalityOfOne.v`.',
    note: 'Theorem positive_nat_is_distinction_count : forall n, (1 <= n)%nat -> distinction_count_from_one n (PrimalityOfOne.v); с 13.11 (замена свидетеля) — ' + CL + '. Совпадение двух счётов — cardinal_and_binary_counts_coincide (' + BC + ').' });
  fix('Весь слой — 7 теорем, *без единой аксиомы*', null, {
    claim: 'Слой `BitString.v` — 7 теорем, слой счёта над ним — файл `BitStringCount.v`; оба *без единой аксиомы*; формальным якорем бинарного пути служат теперь и тип `Side` с $L2$ / $L3$, и построенный над ним `BitString.v`.',
    page_price: 'без единой аксиомы',
    note: 'BitString.v: 7 строк Qed (не менялся); BitStringCount.v: 30 Qed и одно Defined. У всех объявлений обоих файлов Print Assumptions — ' + CL + '; строк Axiom и Parameter нет.' });
  // --- § 4.4.4: нуль и единица
  add({ theorem: 'empty_not_positive_count', file: BC,
    claim: 'Формально: пустая запись положительного счёта не имеет (`empty_not_positive_count`)',
    note: 'empty_not_positive_count : ~ positive_bit_count []. ' + CL + '.' });
  add({ theorem: 'one_bit_is_least_positive_count', file: BC,
    claim: 'а единица — наименьший положительный счёт (`one_bit_is_least_positive_count`).',
    note: 'one_bit_is_least_positive_count : forall bs : BitString, positive_bit_count bs -> bit_length one_bit <= bit_length bs; bit_length one_bit = 1 (one_bit_length). ' + CL + '.' });
  // --- § 4.5: сторона добавления бита
  const C_ADD = 'длина в обоих случаях возрастает ровно на единицу (`add_bit_increments_length`, `add_bit_right_increments_length`)';
  add({ theorem: 'add_bit_right_increments_length', file: BC, claim: C_ADD,
    note: 'add_bit_right_increments_length : forall (b : Bit) (bs : BitString), bit_length (bs ++ [b]) = S (bit_length bs). ' + CL + '.' });
  add({ theorem: 'add_bit_increments_length', file: BSF, claim: C_ADD,
    note: 'add_bit_increments_length : forall b bs, bit_length (add_bit b bs) = S (bit_length bs) (BitString.v:56). ' + CL + '.' });
  // --- § 4.7: индукция
  add({ theorem: 'induction_from_one_bit_misses_empty', file: BC,
    claim: 'свойство было верно для всякой *непустой* двоичной записи, довольно двух вещей',
    note: DONE + ' (развилка — А): вставлено слово «непустой» (здесь и в абзаце «Отсюда и правомерность»). Без него принцип неверен: induction_from_one_bit_misses_empty (' + BC + '), ' + CL + '.' });
  fix('Стандартная индукция по `nat` (или эквивалентная ей индукция по записям через условие', 'nonempty_bitstring_ind', {
    claim: 'Принцип `nonempty_bitstring_ind` лишь записывает его в форме, прямо отвечающей бинарному пути.',
    note: 'nonempty_bitstring_ind (BitString.v:76) — принцип для непустых записей; ' + CL + '.' });
  const C_BOTH = 'даёт тот же результат — это проверено в обе стороны (файл `BitStringCount.v`: `nonempty_bitstring_ind_via_nat`, `nat_ind_from_one_via_bitstrings`);';
  add({ theorem: 'nonempty_bitstring_ind_via_nat', file: BC, claim: C_BOTH,
    note: 'nonempty_bitstring_ind_via_nat — тот же принцип, доказанный индукцией по nat по длине записи. ' + CL + '.' });
  add({ theorem: 'nat_ind_from_one_via_bitstrings', file: BC, claim: C_BOTH,
    note: 'nat_ind_from_one_via_bitstrings : forall Q, Q 1 -> (forall n, 1 <= n -> Q n -> Q (S n)) -> forall n, 1 <= n -> Q n — из nonempty_bitstring_ind. ' + CL + '.' });
  add({ theorem: 'induction_from_one_bit_misses_empty', file: BC,
    claim: 'без условия непустоты принцип неверен — пустая запись им не покрыта (`induction_from_one_bit_misses_empty`).',
    note: 'induction_from_one_bit_misses_empty : ~ (forall P : BitString -> Prop, (forall b, P [b]) -> (forall b bs, P bs -> P (b :: bs)) -> forall bs, P bs). ' + CL + '.' });
  // --- § 4.8: разбор E/R/R
  fix('в коде зафиксированы тип `Side` и леммы $L2$/$L3$ (`Binarity.v`), а слой двоичной записи', null, {
    claim: 'в коде зафиксированы тип `Side` и леммы $L2$/$L3$ (`Binarity.v`), а слой двоичной записи (`Bit`, `BitString`, `bit_length`, `add_bit`, `nonempty_bitstring_ind`) построен поверх него в `BitString.v` (7 теорем, 0 аксиом; § 4.4); счёт сторон, счёт записей и связь с записью `Distinction` — в `BitStringCount.v` и `DistinctionSideRole.v`, тоже без аксиом.',
    page_price: 'без аксиом',
    note: 'BitString.v: 7 Qed; BitStringCount.v: 30 Qed; DistinctionSideRole.v: 8 Qed. У всех объявлений трёх файлов Print Assumptions — ' + CL + '.' });
  fix('По $L1$ каждая сторона тождественна себе (`Side` — тип с разрешимым равенством).', 'Side', {
    theorem: 'Side_eq_dec', file: BC,
    claim: 'По $L1$ каждая сторона тождественна себе (`Side` — тип с разрешимым равенством: `Side_eq_dec`).',
    note: DONE + ' (формализацией): лемма названа. Side_eq_dec : forall a b : Side, {a = b} + {a <> b} (decide equality; Defined). ' + CL + '.' });
  // --- сноска 1
  fix('в файле `BitString.v` (поверх `Binarity.v`) доказана синтетическая теорема `side_binarity', 'side_binarity', {
    theorem: 'side_is_binary', file: BSF,
    claim: 'в файле `BitString.v` (поверх `Binarity.v`) двоичность записана одной пропозицией `side_binarity := Marked <> Unmarked ' + AND + ' (forall s : Side, s = Marked ' + OR + ' s = Unmarked)` и доказана леммой `side_is_binary` (из `L2_exclusive` и `L3_exhaustive`);',
    note: DONE + ': сноска 1. Было «доказана синтетическая теорема side_binarity». side_binarity — Definition (BitString.v:30); Lemma side_is_binary : side_binarity (:33). ' + CL + '.' });
  const C_TWO = 'а для буквального «счёт сторон $=2$» — список `all_sides := [Marked; Unmarked]` с леммами полноты (`all_sides_complete`) и длины (`all_sides_length`: `length all_sides = 2`), к которым в файле `BitStringCount.v` добавлены неповторяемость (`all_sides_nodup`) и теорема `side_count_exactly_two`: всякое перечисление сторон без повторов имеет длину $2$.';
  fix('а для буквального «счёт сторон $=2$» — список `all_sides := [Marked; Unmarked]` с леммами полноты', 'all_sides_complete', {
    claim: C_TWO,
    note: DONE + ' (формализацией): сноска 1. all_sides_complete (BitString.v:39), all_sides_length (:42); «ровно две» теперь доказано счётом — all_sides_nodup и side_count_exactly_two (' + BC + '). ' + CL + '.' });
  add({ theorem: 'side_count_exactly_two', file: BC, claim: C_TWO,
    note: 'side_count_exactly_two : forall l : list Side, NoDup l -> (forall s : Side, In s l) -> length l = 2. ' + CL + '.' });
  add({ theorem: 'all_sides_nodup', file: BC, claim: C_TWO,
    note: 'all_sides_nodup : NoDup all_sides — из L2_exclusive. ' + CL + '.' });
  add({ theorem: 'side_binarity', file: BSF, claim: C_TWO.slice(0, 0) + 'двоичность записана одной пропозицией `side_binarity := Marked <> Unmarked ' + AND + ' (forall s : Side, s = Marked ' + OR + ' s = Unmarked)`',
    note: 'Definition side_binarity : Prop (BitString.v:30) — запись страницы совпадает с исходником.' });
  add({ theorem: 'complete_length_two_is_not_exactly_two', file: BC,
    claim: 'Полнота и длина одни дают только «не больше двух».',
    note: 'Верно: complete_length_two_is_not_exactly_two : exists l : list unit, (forall u, In u l) ' + AND + ' length l = 2 — у типа с одним значением тоже есть полный список длины 2. ' + CL + '. Имя леммы на странице не названо.' });
  save();
}
