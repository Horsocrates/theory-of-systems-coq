// Собирает описание правок шага 3 Части III: глава III.3 «Счётность рациональных чисел» (места 3.1, 3.2) —
// 7 правок — и глава III.2 (место 2.3) — 1 правка. Формализация — src/CountabilityQValues.v.
// «Было» берётся с живых страниц.
// Запуск: node make-step-03-spec.cjs  -> шаг-03-главы-III3-и-III2.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/03 От натуральных к рациональным/';
const REL3 = DIR + '03 Счётность рациональных чисел.md';
const REL2 = DIR + '02 Рациональные числа.md';
const BS = String.fromCharCode(92);
const LR = '$ℕ ' + BS + 'leftrightarrow ℚ$';
const LRT = '$' + BS + 'leftrightarrow$';

function loader(rel) {
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
    return { old: o, neu: o[0].replace(a, () => b).split('\n') };
  };
  return { old, inline };
}
const e3 = []; const e2 = [];
{
  const { old, inline } = loader(REL3);
  // 1. «Это полная биекция…»: чем две формулы доводятся до биекции значений
  e3.push({ old: old('конструктивно и *без единой аксиомы* (`Print Assumptions', 'Q_bijection`: «Closed under the global context»).'),
    neu: ['конструктивно и *без единой аксиомы* (`Print Assumptions',
          'Q_bijection`: «Closed under the global context»). Сами две формулы дают',
          'взаимную обратность прямого и обратного хода; до биекции *значений* их',
          'доводит третье — номер зависит только от значения дроби',
          '(`index_of_Q_Qeq`), — и в полном виде биекция записана теоремой',
          '`Q_bijection_values` (файл `CountabilityQValues.v`, тоже без аксиом).'] });
  // 2. «вместе это и есть биекция рациональных значений»
  e3.push({ old: old('точностью до `Qeq` на $ℚ$; вместе это и есть биекция', 'рациональных *значений*.'),
    neu: ['точностью до `Qeq` на $ℚ$; вместе с тем, что равные дроби получают',
          'один номер (`index_of_Q_Qeq`), это и есть биекция',
          'рациональных *значений* (`Q_bijection_values`).'] });
  // 3. итог раздела
  e3.push({ old: old('`Q_bijection` доказывает их взаимную обратность — полную', 'аксиом) уже для всего $ℚ$.*'),
    neu: ['`Q_bijection` доказывает их взаимную обратность, а теорема',
          '`Q_bijection_values` — полную',
          'биекцию ' + LR + ' (с точностью до `Qeq`, 0',
          'аксиом) уже для всего $ℚ$.*'] });
  // 4. разбор E/R/R, оговорка о статусе
  e3.push({ old: old('теоремы `enum_Q_index_id` и `index_of_Q_enum_id`,', '0 аксиом — с единственной точностью, что $ℚ$ берётся до `Qeq`'),
    neu: ['теоремы `enum_Q_index_id` и `index_of_Q_enum_id` и лемма о том, что',
          'равные дроби получают один номер (`index_of_Q_Qeq`; сводная теорема',
          '`Q_bijection_values`, файл `CountabilityQValues.v`),',
          '0 аксиом — с единственной точностью, что $ℚ$ берётся до `Qeq`'] });
  // 5. правило канона: «всякое значение встречается ровно раз»
  e3.push({ old: old('несократимость (`enum_coprime`) — всякое рациональное', '$1/2$ (§ 3.3). По $P4$ обход есть *процесс*: до всякого'),
    neu: ['несократимость (`enum_coprime`) — в обходе стоят только несократимые',
          'пары, и потому всякое положительное рациональное',
          '*значение* встречается ровно раз (`enum_QPos_each_value_once`), $2/4$ не появляется отдельно от',
          '$1/2$ (§ 3.3). По $P4$ обход есть *процесс*: до всякого'] });
  // 6. место 3.2: строка таблицы
  e3.push(inline('| навигация ' + LRT + ' номер; обратимость | биекция `nat` ' + LRT + ' `QPos` | Rule |',
    'биекция `nat` ' + LRT + ' `QPos`',
    'биекция `nat` ' + LRT + ' несократимые пары `QPos` (`enum_QPos_bijection_coprime`)'));
  // 7. строка таблицы о несократимости
  e3.push(inline('| несократимость (`enum_coprime`) | каждое значение однажды | Rule |',
    '| несократимость (`enum_coprime`) | каждое значение однажды | Rule |',
    '| несократимость (`enum_coprime`) | каждое значение однажды (`enum_QPos_each_value_once`) | Rule |'));
}
{
  const { old } = loader(REL2);
  // 8. III.2, место 2.3
  e2.push({ old: old('они взаимно обратны (с точностью до `Qeq`: $2/4$ и $1/2$ —', 'получают один номер).'),
    neu: ['они взаимно обратны (с точностью до `Qeq`); что равные дроби — $2/4$ и',
          '$1/2$ — получают один номер и что обход не повторяет значений, доказано',
          'отдельно (теорема `Q_bijection_values`, файл `CountabilityQValues.v`).'] });
}
const out = ['@@FILE ' + REL3];
for (const e of e3) out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END');
out.push('@@FILE ' + REL2);
for (const e of e2) out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END');
fs.writeFileSync(path.join(__dirname, 'шаг-03-главы-III3-и-III2.txt'), out.join('\n') + '\n');
console.log('шаг-03-главы-III3-и-III2.txt: правок ' + (e3.length + e2.length));
