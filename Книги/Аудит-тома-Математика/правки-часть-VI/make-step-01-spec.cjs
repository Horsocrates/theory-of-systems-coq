// Собирает описание правок шага 1 Части VI («мера нуль делом»; места 1.4, 2.1, 2.2):
//   шаг-01-главы-VI1-и-VI2.txt        — 4 правки: сноска 14 главы VI.1; определение, сноски 5 и 6 главы VI.2;
//   шаг-01а-несчётность-канторова.txt — 2 правки главы VI.2 (дополнение: несчётность канторова множества
//                                        теперь теорема; вносится отдельным словом автора).
// Формализация — src/process/ProcessNullCovers.v. «Было» берётся с живых страниц.
// Запуск: node make-step-01-spec.cjs   (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/06 Меры и интегрирование/';
const REL1 = DIR + '01 Мера как процесс приписывания.md';
const REL2 = DIR + '02 Мера Лебега на процессном континууме.md';
const BS = String.fromCharCode(92);
const CDOT = BS + 'cdot';

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
  const whole = (prefix, neu) => ({ old: old(prefix, prefix), neu: [neu] });
  return { old, inline, whole };
}

const e1 = []; const e2 = []; const e2a = [];
{
  const { whole } = loader(REL1);
  // 1. VI.1, сноска 14 (место 1.4)
  e1.push(whole('[^14]: Это доказано как процессное утверждение:',
    '[^14]: Доказано, 0 аксиом: вокруг $k$-й точки нумерации на стадии $n$ взят отрезок длины $(1/2)^n' + CDOT + '(1/2)^{k+1}$, всякая конечная сумма длин не превосходит $(1/2)^n$ (`rationals_covering_process`), а эта оценка сходится к нулю (`rationals_cover_to_zero`, `ProcessRationalsNull.v`); отсюда мера нуль рациональных точек отрезка — `segment_rationals_null`. Для канторова множества покрытие иное — $2^n$ отрезков стадии $n$ суммарной длины $(2/3)^n$: `cantor_null`, со сходимостью оценки `cantor_measure_zero` (`ProcessCantorMeasure.v`). Покрытия и определение меры нуль — в файле `ProcessNullCovers.v`; оба построения разбирает следующая глава.'));
}
{
  const { old, inline, whole } = loader(REL2);
  // 2. VI.2, определение меры нуль (место 2.1)
  e2.push(inline('покрывающего процесса, сходящегося к $0$*.',
    'покрывающего процесса, сходящегося к $0$*.',
    'покрывающего процесса, сходящегося к $0$* (в формализации — определение `null_set`, файл `ProcessNullCovers.v`).'));
  // 3. VI.2, сноска 5 (место 2.1)
  e2.push(whole('[^5]: Доказано: покрывающий процесс $(1/2)^n$ сходится к нулю как процесс,',
    '[^5]: Доказано, 0 аксиом (файл `ProcessNullCovers.v`): вокруг $k$-й точки нумерации на стадии $n$ взят отрезок длины $(1/2)^n' + CDOT + '(1/2)^{k+1}$; всякая рациональная точка накрыта, а всякая конечная сумма длин не превосходит $(1/2)^n$ — `rationals_covering_process`; эта оценка сходится к нулю — `rationals_cover_to_zero` (`ProcessRationalsNull.v`). Отсюда `rationals_null` и `segment_rationals_null`; общее правило для множества, исчерпанного последовательностью рациональных точек, — `countable_null`. Именно счётность (нумерация из Главы 3.3) делает суммарный бюджет покрытия суммируемым.'));
  // 4. VI.2, сноска 6 (место 2.2)
  e2.push(whole('[^6]: Доказано: процесс покрытия $(2/3)^n$ сходится к нулю,',
    '[^6]: Доказано, 0 аксиом (файл `ProcessNullCovers.v`): стадия $n$ состоит ровно из $2^n$ отрезков длины $3^{-n}$ (`cantor_stage_count`), их суммарная длина равна $(2/3)^n$ (`cantor_stage_total`), стадии вложены (`stage_nested`); множество — точки, лежащие во всех стадиях (`in_cantor`); покрывающий процесс — `cantor_covering_process`, мера нуль — `cantor_null`. Оценка $(2/3)^n$ сходится к нулю — `cantor_measure_zero` (`ProcessCantorMeasure.v`).'));

  // Дополнение (отдельным словом автора): несчётность канторова множества — теорема
  // 5. абзац о несчётности
  e2a.push({ old: old('несчётно* — имеет мощность континуума. В настоящей процессной линии доказана лишь',
                      'отдельной Rocq-теоремы о мощности именно канторова множества здесь не используется.'),
    neu: ['несчётно* — имеет мощность континуума. В процессной линии доказана его *мера нуль*',
          'и несчётность в смысле Главы 4.4: всякий код из цифр $0$ и $2$ называет точку',
          'множества (`cantor_point_in_cantor`), разные коды называют разные точки',
          '(`cantor_points_distinct`), и никакая последовательность кодов не называет их все —',
          'диагональный код даёт точку множества, отличную от каждой перечисленной',
          '(`cantor_points_not_enumerable`, файл `ProcessNullCovers.v`). Мощность континуума',
          'остаётся классическим чтением: последовательностей произвольных процессов, не',
          'заданных кодами, теорема не касается.'] });
  // 6. «Несчётно — но меры нуль»
  e2a.push({ old: old('*мера* — какую суммарную ширину они занимают. Канторово множество классически',
                      'несчётно по первому вопросу и *доказуемо* нулево по второму. Смешать их — ошибка'),
    neu: ['*мера* — какую суммарную ширину они занимают. Канторово множество',
          'несчётно по первому вопросу и нулево по второму — и то и другое доказано',
          '(`cantor_not_enumerable_and_null`). Смешать их — ошибка'] });
}

function emit(name, groups) {
  const out = []; let n = 0;
  for (const [rel, edits] of groups) {
    if (!edits.length) continue;
    out.push('@@FILE ' + rel);
    for (const e of edits) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
  }
  fs.writeFileSync(path.join(__dirname, name), out.join('\n') + '\n');
  console.log(name + ': правок ' + n);
}
emit('шаг-01-главы-VI1-и-VI2.txt', [[REL1, e1], [REL2, e2]]);
emit('шаг-01а-несчётность-канторова.txt', [[REL2, e2a]]);
