// Собирает описание правок шага 2 Части X (глава X.1, строки 1–3 таблицы): четыре места.
// Строка 4 таблицы («сравнение мощностей без выбора») правки страницы не требует: после шага 1 слова
// опираются на теорему Schroeder_Bernstein_definite.
// Запуск: node make-step-02-spec.cjs  -> шаг-02-глава-X1.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const REL = 'Направления/Математика/Том Математика/10 Теория множеств без аксиомы выбора/01 Множество как Система, а не объект.md';
const page = fs.readFileSync(LIVE + REL, 'utf8').replace(/\r/g, '').split('\n');
function old(first, last) {
  const hits = page.filter((l) => l.startsWith(first)).length;
  const i = page.findIndex((l) => l.startsWith(first));
  if (i < 0 || hits !== 1) throw new Error('начало не найдено однозначно (' + hits + '): ' + first);
  let j = i; while (j < page.length && !page[j].startsWith(last)) j++;
  if (j >= page.length || j - i > 20) throw new Error('конец не найден: ' + last);
  return page.slice(i, j + 1);
}
function inline(prefix, a, b) {
  const o = old(prefix, prefix);
  if (o[0].split(a).length !== 2) throw new Error('фрагмент в строке не найден однозначно: ' + a);
  return { old: o, neu: [o[0].replace(a, () => b)] };
}
const edits = [
  // 1. строка 3 таблицы: корректность
  { old: old('**Корректность.** Система корректна $\\Longleftrightarrow$ её критерий-домен строго', 'построению*.'),
    neu: ['**Корректность.** Система корректна $\\Longleftrightarrow$ её критерий-домен строго',
          'ниже (P2); фундированность $\\ll$ исключает циклы по уровням и бесконечный спуск *по',
          'построению*.'] },
  // 2. строка 3 таблицы: что даёт
  inline('**Что даёт.** Фундирование $\\to$ теорема (`level_lt_irrefl`)',
    'Фундирование $\\to$ теорема (`level_lt_irrefl`);',
    'Фундирование $\\to$ теорема (`level_lt_wf`: порядок уровней фундирован; в форме самой аксиомы — `level_foundation_form`);'),
];
// 3–4. строки 1 и 2 таблицы: сноски 3 и 4
{
  const o3 = old('[^3]: `russell_paradox_blocked` (`TheoryOfSystems_Core_ERR.v`)', '[^3]: `russell_paradox_blocked` (`TheoryOfSystems_Core_ERR.v`)');
  edits.push({ old: o3, neu: ['[^3]: `russell_blocked_every_level` (`foundation/TransfiniteInductionLevel.v`): ни на каком уровне нет системы, собирающей в точности те системы этого уровня, что не входят в себя, — каким бы ни было отношение принадлежности. Про сам критерий — `criterion_label_never_own_level`: уровень критерий-домена никогда не равен уровню системы (для $L_2$ это `russell_paradox_blocked` в `TheoryOfSystems_Core_ERR.v`). См. также `P4ProhibitsImpredicative.v`: собиратель расселова условия по области сам в эту область не входит (`russell_collector_escapes`), поэтому область, у которой такой собиратель есть, не завершена (`russell_needs_incomplete_range`). Всё — без аксиом.'] });
  const o4 = old('[^4]: `P4ProhibitsImpredicative.v`: $R$ требует completed totality', '[^4]: `P4ProhibitsImpredicative.v`: $R$ требует completed totality');
  edits.push({ old: o4, neu: ['[^4]: `P4ProhibitsImpredicative.v`: по каждой конечной стадии собиратель расселова условия существует, лежит вне стадии и появляется на следующей (`staged_russell_collector_exists`); противоречие возникает, только когда область обязана содержать собственный собиратель, то есть быть завершённой (`russell_requires_completed_totality`). Что P4 исключает завершённую область — `completed_inf_contradicts_P4` (`P4CompletedInfinity.v`), при условии `bridge`: все члены области актуальны уже на начальной стадии (см. Главу 4.1).'] });
}
const out = ['@@FILE ' + REL];
for (const e of edits) out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END');
fs.writeFileSync(path.join(__dirname, 'шаг-02-глава-X1.txt'), out.join('\n') + '\n');
console.log('описание собрано: правок ' + edits.length);
