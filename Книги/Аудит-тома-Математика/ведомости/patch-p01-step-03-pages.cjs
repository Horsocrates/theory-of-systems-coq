// Часть I, шаг 3, страницы (2026-11-13, слово автора «Делай»): 16 правок главы I.2 внесены.
// Запуск: node patch-p01-step-03-pages.cjs   (затем relocate + merge по part01-ch02)
// Скрипт повторяем: приведённая запись пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть I, шаг 3, слово автора)';
const F = 'src/foundation/';
const CD = F + 'DistinctionCoDefinition.v';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  return {
    fix(prefix, th, fields, keepVerdict) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) &&
        (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
      if (hit.length === 0) return;
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix.slice(0, 50) + '» / ' + th + ', найдено ' + hit.length);
      Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
    },
    add(rec) {
      if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); },
  };
}
const a = open('part01-ch02.json');
// место 1
a.fix('Общая запись, стало быть, шире канонической конструкции: она оставляет', 'Distinction', {
  theorem: 'negative_iff_not_positive', file: CD, page_price: 'без аксиом',
  claim: 'Общая запись, стало быть, шире канонической конструкции по форме: она оставляет отрицательную сторону явной частью акта, не сводя её заранее к отрицанию положительной. По содержанию же поля `exclusive` и `exhaustive` связывают стороны жёстко: во всякой записи отрицательная сторона равносильна отрицанию положительной (`negative_iff_not_positive`, файл `DistinctionCoDefinition.v`, без аксиом).',
  note: DONE + ': было «общая запись этого не требует». negative_iff_not_positive : forall D, negative D <-> ~ positive D. Closed under the global context. С ценой classic: every_distinction_canonical_up_to_iff — всякое различение совпадает с каноническим с точностью до равносильности сторон.' });
// место 2
a.fix('Здесь зафиксируем лишь: $\\varepsilon$ и $\\eta$ несут *структурную* информацию', 'Distinction', {
  claim: 'Здесь зафиксируем лишь: $\\varepsilon$ и $\\eta$ — термы доказательств, которыми исключительность и исчерпанность установлены в данном различении; они не сводятся к булевским значениям «true/false».',
  note: DONE + ': было «несут структурную информацию — они показывают, как… установлены». При принятой classic доказательства в полях неразличимы (distinction_proof_fields_irrelevant, цена — Distinction.classic).' });
a.fix('В настоящем томе используется стандартная CIC, где `Prop` по умолчанию *не* обладает строгой proof-irrelevance, но', null, {
  claim: 'В настоящем томе используется стандартная CIC, где `Prop` по умолчанию *не* обладает строгой proof-irrelevance; с аксиомой `classic`, принятой в томе, она становится теоремой',
  note: DONE + ': было «но в большинстве конкретных рассуждений мы можем её принимать». ClassicalFacts.proof_irrelevance_cci : (forall A, A \\/ ~ A) -> forall (B : Prop) (b1 b2 : B), b1 = b2; применена в distinction_proof_fields_irrelevant.' }, true);
a.fix('Но *сама структура* объекта `Distinction` — *релевантна*. Разные акты различения', 'Distinction', {
  claim: 'Но *сама структура* объекта `Distinction` — *релевантна*. Разные акты различения, даже если они приводят к одному и тому же абстрактному факту, могут быть *структурно различны*: разные положительные стороны, разные отрицательные стороны.',
  note: DONE + ': из перечня убрано «разные обоснования исключительности и исчерпанности»; следом сказано, что обоснования актов не различают.' });
a.add({ theorem: 'distinction_determined_by_sides', file: CD, page_price: 'classic',
  claim: 'Обоснования исключительности и исчерпанности запись тоже хранит, но актов они не различают: при принятой аксиоме `classic` различение определяется своими двумя сторонами (`distinction_determined_by_sides`, файл `DistinctionCoDefinition.v`; цена — `classic`).',
  note: 'distinction_determined_by_sides : positive D1 = positive D2 -> negative D1 = negative D2 -> D1 = D2. Axioms: Distinction.classic.' });
// место 6
a.fix('В Части IV — запись `CauchyProcess` как процесс с полем сходимости.', 'CauchyProcess', {
  theorem: 'CauchySeq', file: 'src/CauchyReal.v',
  claim: 'В Части IV — запись `CauchySeq` как процесс с полем сходимости.',
  note: DONE + ': было `CauchyProcess` — такого объявления нет. Record CauchySeq := mkCauchy { cs_seq :> nat -> Q; cs_cauchy : is_cauchy cs_seq } (CauchyReal.v:48).' });
// место 8
a.fix('В Части XII — запись `Category` как структура с объектами', 'Category', {
  claim: 'В Части XIV — запись `Category` как структура с объектами, морфизмами, композицией и полями ассоциативности и тождества.',
  note: DONE + ': было «В Части XII». Запись Category (stdlib/Category.v:23) разбирается в главе 14.1.' });
a.fix('**Часть XII: категорная теория.**', null, { claim: '**Часть XIV: категорная теория.**',
  note: DONE + ': было «Часть XII». Часть XIV — «Категория систем».' });
a.fix('**Часть XV: квантовая информация.**', null, { claim: '**Части VI и XVII: квантовая теория и информация.**',
  note: DONE + ': было «Часть XV: квантовая информация» — части с таким предметом в томе нет (Часть XV — «Вычисления и граница финитизации»). Глава 6.6 — операторы и мост в квантовую динамику; глава 17.7 — раздел «Фон-Нейман и квантовая информация: мост к физике».' });
a.fix('В Главе 6 (Часть I) — тип `Level` как самостоятельная структура', 'Level', {
  claim: 'В Главе 3 (Часть I) — тип `Level` как самостоятельная структура для формализации Закона Порядка $L5$.',
  note: DONE + ': было «В Главе 6». Тип Level вводится в главе 3 (раздел «Формальный аппарат: тип Level»).' });
// место 5
a.fix('Definition distinction_of (P : Prop) : Distinction := mkDistinction P (~ P) _ _.', 'distinction_of', {
  note: DONE + ': подпись блока — «Схема определения distinction_of в Rocq» (было «Формальное определение»). Блок с подчёркиваниями — заготовка: компилятор как определение его не принимает, и страница ниже сама называет подчёркивания обязательствами доказательства.' });
a.fix('Definition distinction_of (P : Prop) : Distinction. Proof. apply (mkDistinction P (~ P)).', 'distinction_of', {
  note: DONE + ': подпись блока — «полное определение можно записать в Rocq по шагам» (было «имеет вид»); после разбора добавлено, что в репозитории тот же объект записан одним термом и что равенство двух записей доказано (distinction_of_by_steps_eq). Print Assumptions distinction_of: Distinction.classic.' });
a.fix('`apply (mkDistinction P (~ P)).` — применяем конструктор `mkDistinction`', 'mkDistinction', {
  note: DONE + ': разбор относится к пошаговой записи; страница теперь называет её пошаговой и говорит, что в репозитории объект записан одним термом.' });
a.add({ theorem: 'distinction_of_by_steps_eq', file: CD,
  claim: 'Обе записи дают одно и то же определение — равенство проверяется вычислением (`distinction_of_by_steps_eq`, файл `DistinctionCoDefinition.v`).',
  note: 'distinction_of_by_steps_eq : forall P, distinction_of_by_steps P = distinction_of P (доказательство — reflexivity). Axioms: Distinction.classic (через distinction_of).' });
// место 7
a.fix('Lemma no_contradiction_P : forall P : Prop, ~(P /\\ ~ P).', 'no_contradiction_P', {
  theorem: 'L2_constructive', file: F + 'BinarityVsTotality.v',
  claim: 'Theorem L2_constructive : forall P : Prop, ~ (P /\\ ~ P). Proof. intros P [p np]. exact (np p). Qed.',
  note: DONE + ': было `Lemma no_contradiction_P` — такого имени нет. L2_constructive (BinarityVsTotality.v:85) — то же утверждение с тем же доказательством. Closed under the global context.' });
// место 3
a.fix('Из `distinction_of` будут выведены законы логики $L1, L2, L3, L4$', 'distinction_of', {
  claim: 'Из записи `Distinction` будут выведены законы логики $L1, L2, L3, L4$ как теоремы о её свойствах; `distinction_of` приносит эти теоремы к каждой пропозиции.',
  note: DONE + ': было «Из distinction_of будут выведены законы». Теоремы о законах сформулированы о произвольной записи D; distinction_of в них не участвует.' });
// место 4
a.fix('В Части III — структуры отношений между различениями, опирающиеся на `Distinction`', 'Distinction', {
  claim: 'В Части II — структуры отношений между различениями, опирающиеся на `Distinction` как на базовый объект, но вводящие свою собственную надстройку (счёт как длина списка различений).',
  note: DONE + ': было «В Части III». Файлы Части III запись Distinction не подключают; надстройка — distinction_count (Distinction.v:157), глава II.2.' });
a.fix('В Части XI — алгебраические структуры (группы, кольца), в которых `Distinction` используется опосредованно', 'Distinction', {
  claim: 'В Части XI — алгебраические структуры (группы, кольца): записи того же вида — носитель и поля-обоснования свойств элементов и операций. Сама запись `Distinction` в них не используется; акт различения присутствует в них опосредованно — каждое поле-свойство есть пропозиция.',
  note: DONE + ': было «в которых Distinction используется опосредованно». Файлы Части XI (stdlib/GroupTheory.v, stdlib/RingField.v, src/algebra/*) запись Distinction не подключают ни прямо, ни через зависимости.' });
a.save();
