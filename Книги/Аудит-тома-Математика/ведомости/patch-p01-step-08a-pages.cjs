// Часть I, шаг 8а (2026-11-13, слово автора «Продолжай» на сообщение с шестью правками четырёх отставших страниц):
// правки внесены; в ведомости I.6 четыре записи абзаца стр. 228–245 приведены к новым словам.
// Запуск: node patch-p01-step-08a-pages.cjs  (затем relocate + merge по part01-ch06). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть I, шаг 8а, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part01-ch06.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
const fix = (prefix, fields) => { const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix)); if (!hit.length) return; if (hit.length !== 1) throw new Error('не одна запись: ' + prefix); Object.assign(hit[0], { verdict: 'ok' }, fields); n++; };
const BS = String.fromCharCode(92);
fix('Логически в проекте *два* предполагаемых аксиоматических объявления', { claim: 'Логически в проекте *два* аксиоматических объявления — $L3$ и $L4$.' });
fix('Технически же $L3$ зарегистрирован не в одном месте', { external: true, page_price: 'местные объявления сняты',
  claim: 'Технически $L3$ долгое время был зарегистрирован не в одном месте: помимо реэкспорта из `ToS_Axioms.v`, в двух файлах — `Distinction.v` и `BorelDeterminacy.v` — он был объявлен *локально*, прямой строкой `Axiom classic : forall P : Prop, P ' + BS + '/ ~ P`.',
  note: DONE + ': абзац переведён в прошедшее время — местные объявления `Axiom classic` в Distinction.v и BorelDeterminacy.v сняты 13.11; оба файла подключают объявление стандартной библиотеки.' });
fix('Поэтому тезис «всё сверх платформы CIC помещается в два объявления» следует понимать', {
  claim: 'Поэтому тезис «всё сверх платформы CIC помещается в два объявления» верен и *логически* (два закона — $L3$ и $L4$), и по строкам кода: строка `Axiom` в репозитории одна — `L4_witness`, а `classic` приходит из стандартной библиотеки.',
  note: DONE + ': было «следует понимать логически…, а не как утверждение, что в коде ровно две физические строки Axiom». Строк Axiom в src одна (ToS_Axioms.v:105); строк Parameter нет.' });
fix('Это — место, которое в репозитории стоит синхронизировать', {
  claim: 'С ноября 2026 года они сняты: оба файла подключают объявление стандартной библиотеки — то же, которое реэкспортирует `ToS_Axioms.v`, — и `Print Assumptions` называет для $L3$ одну аксиому.',
  note: DONE + ': было «место, которое в репозитории стоит синхронизировать» — синхронизация выполнена. Полный обход допущений 13.11: имён аксиом в ответах компилятора два — Classical_Prop.classic и ToS_Axioms.L4_witness.' });
const NEWC = 'Тогда же объявления раздела Навье — Стокса (две аксиомы и два параметра о коэффициентах нелинейного члена) переведены в посылки: теоремы раздела получают их аргументом.';
if (!j.records.some((r) => norm(r.claim) === norm(NEWC))) { j.records.push({ line: 0, theorem: null, claim: NEWC, page_price: '', verdict: 'ok',
  note: 'Запись посылок — класс NSCoupling (src/navier_stokes/GalerkinSystem.v) с полями B_raw, C_B, C_B_positive, B_raw_antisym_bounded; 32 файла раздела получают её неявным аргументом. NSCoupling_inhabited, B_coeff_bounded, millennium_reading2_capstone — Closed under the global context.' }); added++; }
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part01-ch06.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
