// Шаг 1б Части II: развилка «свидетель», слово автора «А» (13.11.2026). В теоремах о счёте свидетель
// `distinction_of True` заменён различением «истина | ложь» (`distinction_true_false`); на страницах меняется
// имя свидетеля. Без ключа — два места, показанные автору (II.1, блок first_count_is_one; II.2, абзац
// «Чем различаются повторения акта»). С ключом --rest — ещё два упоминания в II.2 (блок и фраза § 2.4),
// найденные при внесении; вносятся после показа автору.
// Запуск: node make-step-01b-spec.cjs [--rest]  -> шаг-01б-свидетель.txt | шаг-01в-свидетель-II2.txt
const fs = require('fs');
const path = require('path');
const REST = process.argv.includes('--rest');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const T = 'Направления/Математика/Том Математика/02 Натуральные числа/';
function pageOf(rel) {
  const page = fs.readFileSync(LIVE + rel, 'utf8').replace(/\r/g, '').split('\n');
  const old = (first, last, max) => {
    const hits = page.filter((l) => l.startsWith(first)).length;
    const i = page.findIndex((l) => l.startsWith(first));
    if (i < 0 || hits !== 1) throw new Error(rel + ': начало не найдено однозначно (' + hits + '): ' + first);
    let j = i; while (j < page.length && !page[j].startsWith(last)) j++;
    if (j >= page.length || j - i > (max || 20)) throw new Error(rel + ': конец не найден: ' + last);
    return page.slice(i, j + 1);
  };
  const inline = (prefix, a, b) => {
    const o = old(prefix, prefix);
    if (o[0].split(a).length !== 2) throw new Error(rel + ': фрагмент в строке не найден однозначно: ' + a.slice(0, 60));
    return { old: o, neu: [o[0].replace(a, () => b)] };
  };
  return { old, inline };
}
const out = [];
const section = (rel, edits) => { out.push('@@FILE ' + rel); for (const e of edits) out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); };
let n = 0;
if (!REST) {
  const p1 = pageOf(T + '01 Первичность единицы.md');
  section(T + '01 Первичность единицы.md', [
    p1.inline('  exists (cons (distinction_of True) nil).', '(cons (distinction_of True) nil)', '(cons distinction_true_false nil)'),
  ]); n += 1;
  const p2 = pageOf(T + '02 Счёт как длина списка различий.md');
  section(T + '02 Счёт как длина списка различий.md', [
    { old: p2.old('предъявляет `[distinction_of True]`, а', '`[distinction_of True; distinction_of True; distinction_of True]` —'),
      neu: ['предъявляет `[distinction_true_false]`, а',
            '`succ_is_new_distinction` присоединяет',
            '`distinction_true_false` к уже имеющемуся списку. Список из трёх',
            'различий есть, таким образом,',
            '`[distinction_true_false; distinction_true_false; distinction_true_false]` —'] },
  ]); n += 1;
} else {
  const p2 = pageOf(T + '02 Счёт как длина списка различий.md');
  section(T + '02 Счёт как длина списка различий.md', [
    p2.inline('  exists [distinction_of True].', '[distinction_of True]', '[distinction_true_false]'),
    p2.inline('различия — `[distinction_of True]`, список с', '`[distinction_of True]`', '`[distinction_true_false]`'),
  ]); n += 2;
}
const name = REST ? 'шаг-01в-свидетель-II2.txt' : 'шаг-01б-свидетель.txt';
fs.writeFileSync(path.join(__dirname, name), out.join('\n') + '\n');
console.log(name + ': правок ' + n);
