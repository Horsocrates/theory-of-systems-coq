// Собирает описание правок шага 7 Части X (глава X.6, строки 6–11 таблицы): восемь мест в главе X.6
// и одно место в главе IV.1 (поправка неточности, внесённой на шаге 6).
// Запуск: node make-step-07-spec.cjs [A|B]  -> шаг-07-глава-X6.txt (формат tools/apply-edits.cjs)
//   A — прежний классический путь леммы Диксона снят из HigmanLemma.v (16 Qed); B — оставлен (18 Qed).
const fs = require('fs');
const path = require('path');
const variant = (process.argv[2] || 'A').toUpperCase();
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
function pageOf(rel) {
  const page = fs.readFileSync(LIVE + rel, 'utf8').replace(/\r/g, '').split('\n');
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
  return { old, inline };
}
const M = 'Направления/Математика/Том Математика/';
const X6 = M + '10 Теория множеств без аксиомы выбора/06 Синтез Части X что доказуемо без выбора, и карта границ.md';
const IV1 = M + '04 Процессные действительные числа/01 P4 бесконечность как процесс.md';
const blocks = [];
function file(rel, edits) { blocks.push('@@FILE ' + rel); for (const e of edits) blocks.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); return edits.length; }
let total = 0;
const FN1 = variant === 'A'
  ? '[^1]: `HigmanLemma.v`: `is_wqo`, `wqo_nat_le`, `higman_unit` (списки над однобуквенным алфавитом), `dickson_pair` (лемма Диксона для пар, доказана конструктивно), `wqo_nat_pair`, итог — `higman_synthesis`. 16 Qed, 0 аксиом.'
  : '[^1]: `HigmanLemma.v`: `is_wqo`, `wqo_nat_le`, `higman_unit` (списки над однобуквенным алфавитом), `dickson_pair` (лемма Диксона для пар, доказана конструктивно), `wqo_nat_pair`, итог — `higman_synthesis`; все они — без допущений. 18 Qed; `classic` остаётся только под двумя леммами прежнего доказательства, которые ничем не используются.';
{
  const a = pageOf(X6);
  const e = [
    // 1. строки 7, 8, 10, 11 таблицы: что доказано
    { old: a.old('проводит без выбора и более «высокие» результаты. *Лемма Хигмана*: списки над конечным', 'определена.[^4]'),
      neu: ['проводит без выбора и более «высокие» результаты. *Лемма Хигмана*: списки над конечным',
            'алфавитом образуют хорошо-квазиупорядочение (wqo) — доказан случай однобуквенного алфавита',
            '(он сводится к wqo на длинах); рядом доказаны wqo для самих $\\mathtt{bool}$ и $ℕ$ и лемма',
            'Диксона для пар.[^1]',
            '*Теорема Крускала*: конечные деревья wqo под гомеоморфным вложением — доказано для',
            'конкретных семейств (цепи, вилки, деревья глубины',
            '$\\le 1$).[^2] *Кантор–Бендиксон*: производная',
            'множества как процесс; $\\omega$-предел итераций содержит всякое совершенное подмножество, а',
            'при стабилизации на конечном шаге совпадает с совершенным ядром.[^3] И *конечная',
            'детерминированность игр* (Цермело, 1913): в игре конечной длины выигрышная стратегия есть',
            'у одного из игроков.[^4]'] },
    // 2. строки 6 и 8: честная мера
    { old: a.old('конкретных семейств* без выбора — но *не* в полной общности. Это и подводит к карте', 'границ.'),
      neu: ['конкретных семейств* без выбора — но *не* в полной общности. Одна оговорка:',
            'детерминированность игр с бесконечным числом ходов на каждом шаге требует извлечь',
            'стратегию и потому стоит на L3 и L4, взятом в полную силу; для конечных деревьев игры она',
            'доказана без допущений. Это и подводит к карте',
            'границ.'] },
    // 3. курсив
    { old: a.old('*Без выбора доказуемы и wqo-результаты (Хигман, Крускал — для конкретных семейств) и', 'полная общность.*'),
      neu: ['*Без выбора доказуемы wqo-результаты (Хигман — для однобуквенного алфавита, Крускал — для',
            'конкретных семейств) и детерминированность конечных деревьев игры; для игр конечной длины с',
            'бесконечным числом ходов стратегию приходится извлекать — ценой L3 и L4. Это ядра «высоких»',
            'теорем, не их полная общность.*'] },
  ];
  // 4–7. сноски 1–4
  e.push({ old: a.old('[^1]: `HigmanLemma.v`: `is_wqo`', '[^1]: `HigmanLemma.v`: `is_wqo`'), neu: [FN1] });
  e.push({ old: a.old('[^2]: `KruskalFull.v`/`KruskalTree.v`:', '[^2]: `KruskalFull.v`/`KruskalTree.v`:'),
    neu: ['[^2]: `KruskalTree.v`: `kruskal_chains`, `kruskal_forks` — любая последовательность цепей, любая последовательность вилок; `KruskalFull.v`: `depth1_wqo` (звёзды), `depth_le1_wqo` (деревья глубины $\\le 1$, листья и звёзды вперемешку). 19 и 12 Qed, 0 аксиом.'] });
  e.push({ old: a.old('[^3]: `CantorBendixsonFull.v`: `CB_deriv`', '[^3]: `CantorBendixsonFull.v`: `CB_deriv`'),
    neu: ['[^3]: `CantorBendixsonFull.v`: `CB_deriv` (точки накопления), `CB_iter`, `CB_omega` ($\\omega$-предел). Всякое совершенное подмножество лежит в $\\omega$-пределе (`perfect_kernel_in_omega`); при стабилизации на конечном шаге этот шаг совершенен и совпадает с $\\omega$-пределом (`stable_stage_is_perfect_kernel`); всякое конечное множество рассеяно (`finite_set_scattered`). В общем случае $\\omega$-предел совершенным ядром не является: ядро достигается продолжением итерации вдоль нотаций (`CB_ord`). 35 Qed, 0 аксиом.'] });
  e.push({ old: a.old('[^4]: `BorelDeterminacy.v`: `weak_determinacy`', '[^4]: `BorelDeterminacy.v`: `weak_determinacy`'),
    neu: ['[^4]: `ZermeloDeterminacy.v`: `zermelo_determinacy` — при любом условии выигрыша и любом числе раундов стратегия есть у одного из игроков; цена — `classic` и `L4_witness` (ходов бесконечно много, стратегию приходится извлекать). `BorelDeterminacy.v`: `weak_determinacy` — исключённое третье для «у первого игрока есть стратегия», и частные случаи (`zero_game_determined`); 19 Qed, 1 аксиома (`classic`). Для конечных деревьев игры — без допущений: `finite_game_strategically_determined` (`foundation/FiniteGameDeterminacy.v`). NB: вопреки имени файла `BorelDeterminacy.v`, борелевская (Мартина) детерминированность здесь не доказана.'] });
  // 8. сноска 7: строка 9 таблицы
  e.push(a.inline('[^7]: Откат закреплён машинно (0 аксиом каждый)',
    '`foundation/FiniteGameDeterminacy.v` (`finite_game_determined`, обратная индукция)',
    '`foundation/FiniteGameDeterminacy.v` (`finite_game_strategically_determined`: каждая позиция конечного дерева выиграна ровно одной стороной, и обратная индукция `mover_wins` вычисляет, какой)'));
  total += file(X6, e);
}
{
  const b = pageOf(IV1);
  total += file(IV1, [
    { old: b.old('функцию, без каких-либо свойств. Все утверждения файла верны для любой', 'такой таблицы и допущений не имеют. Доказано и то, что ни одна таблица'),
      neu: ['функцию, без каких-либо свойств. Все утверждения файла верны для любой',
            'такой таблицы; допущений они не имеют, кроме одной леммы на исключённом',
            'третьем (`pi11_negation`). Доказано и то, что ни одна таблица'] },
  ]);
}
fs.writeFileSync(path.join(__dirname, 'шаг-07-глава-X6.txt'), blocks.join('\n') + '\n');
console.log('описание собрано (вариант ' + variant + '): правок ' + total);
