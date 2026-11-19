// Собирает описание правок шага 3 Части VII («Вентиль Адамара над Q[sqrt 2]»; место 2.1): 9 правок главы VII.2.
// Формализация — src/process/ProcessHadamardGateSqrt2.v. «Было» берётся с живой страницы.
// Запуск: node make-step-03-spec.cjs  -> шаг-03-глава-VII2.txt (формат tools/apply-edits.cjs)
// Внимание: строки с настоящим знаком параграфа через L() не пропускать.
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/07 Гармонический анализ/';
const REL2 = DIR + '02 Уолш–Адамар преобразование без трансцендентностей.md';
const BS = String.fromCharCode(92);
const L = (s) => s.split('§').join(BS);   // «§» в строках ниже — обратная косая черта

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
  const whole = (prefix, neu) => ({ old: old(prefix, prefix), neu: Array.isArray(neu) ? neu : [neu] });
  return { old, inline, whole };
}

const e2 = [];
{
  const { old, inline, whole } = loader(REL2);
  // 1. «что доказано»: вентиль — над расширенным носителем
  e2.push({ old: old('до масштаба, $H(Hf)=N f$. Наконец, нормированный случай $N=2$, если вынести', 'квантовый вентиль Адамара.'),
    neu: ['до масштаба, $H(Hf)=N f$. Наконец, нормированный случай $N=2$ — это в точности',
          L('квантовый вентиль Адамара: множитель $s=1/§sqrt2$ с соотношением $s^2§cdot2=1$ не'),
          'рационален, и вентиль построен над расширенным носителем ℚ[√2] — парами рациональных',
          L('чисел $a+b§sqrt2$.')] });
  // 2. раздел о вентиле: над каким носителем доказаны две черты
  e2.push({ old: old('алгоритмах Гровера, Дойча–Йожи и др.). Две его определяющие черты доказаны как', 'абстрактный параметр.'),
    neu: ['алгоритмах Гровера, Дойча–Йожи и др.). Две его определяющие черты доказаны точно —',
          L('над носителем ℚ[√2], где единственная иррациональность, $§sqrt2$, есть элемент: пара'),
          'рациональных чисел. Над самим ℚ такого вентиля нет: при рациональном множителе $s$',
          'дважды применённый вентиль есть умножение на $2s^2$, а $2s^2=1$ в ℚ неразрешимо.'] });
  // 3. суперпозиция: квадрат амплитуды рационален
  e2.push(inline(L('амплитудами $1/§sqrt2$ на обоих исходах.[^9]'),
    'на обоих исходах.[^9]', 'на обоих исходах; квадрат амплитуды рационален: $1/2$.[^9]'));
  // 4. итоговый курсив раздела
  e2.push({ old: old('структура вентиля (инволюция, суперпозиция) рациональна.*', 'структура вентиля (инволюция, суперпозиция) рациональна.*'),
    neu: ['структура вентиля (инволюция, суперпозиция) доказана над ℚ[√2], а в ℚ остаются',
          '$H(Hf)=2f$ и квадрат амплитуды $1/2$.*'] });
  // 5. разбор E/R/R: «не актуализируются» — над ℚ
  e2.push(inline(L('$1/§sqrt N$ для нечётного $k$ не актуализируются.'),
    'для нечётного $k$ не актуализируются.', 'для нечётного $k$ над ℚ не актуализируются.'));
  // 6. сноска 1: новый файл
  e2.push(inline('[^1]: Опорный файл — `ProcessWalshHadamard.v`',
    '`ProcessHadamardGate.v` (5 утверждений) и `ProcessOrthogonalWalsh.v` (32 утверждения).',
    '`ProcessHadamardGate.v` (5 утверждений), `ProcessOrthogonalWalsh.v` (32 утверждения) и `ProcessHadamardGateSqrt2.v` (14 утверждений).'));
  // 7. сноска 7: обратное преобразование
  e2.push(inline('[^7]: `walsh_HH` в `ProcessFourierON.v`',
    L('и симметрии $H$.'),
    L('и симметрии $H$. В виде обратного преобразования, $H§big(§tfrac1N Hf§big)=f$ при всяком $N=2^k$, — `walsh_inverse` (`ProcessHadamardGateSqrt2.v`).')));
  // 8. сноска 8: инволюция
  e2.push(whole('[^8]: `hgate_involution` в `ProcessHadamardGate.v`',
    L('[^8]: `hgateR_involution` в `ProcessHadamardGateSqrt2.v`: над ℚ[√2] — парами $a+b§sqrt2$ из `CliffordField.v`, где $s=1/§sqrt2$ есть пара $(0,1/2)$ и соотношение $s^2§cdot2=1$ выполнено (`s2_relation_holds`), — дважды применённый вентиль возвращает состояние; посылок теорема не берёт. В `ProcessHadamardGate.v` параметр $s$ рационален, а рационального $s$ с $s^2§cdot2=1$ нет (`hgate_premise_unsat`): при рациональном множителе дважды применённый вентиль есть умножение на $2s^2$ (`hgate_sq_scale`) и тождественным не бывает (`hgate_never_involution_over_Q`). Рациональная форма обратимости — $§tfrac12 H(Hf)=f$ (`half_HH_is_identity`). Тот же вентиль в матричной записи — `mH_invol` (`CliffordField.v`), связь — `hgateR_rows`. Сами элементы $H_2$ — из $§{§pm1§}$ (`hadamard_2x2`). 0 аксиом.')));
  // 9. сноска 9: суперпозиция
  e2.push(whole('[^9]: `hgate_superposition`:',
    '[^9]: `hgateR_superposition`: над ℚ[√2] вентиль переводит $e_0$ в $(s,s)$ — равные амплитуды на двух координатах; квадрат амплитуды — рациональное $1/2$ (`s2_sq_half`); сумма квадратов амплитуд сохраняется для любого состояния (`hgateR_isometry`). В `ProcessHadamardGate.v` равенство `hgate_superposition` верно для любого рационального множителя и нормировки не использует. Это и есть переход от определённого состояния к суперпозиции, выполняемый вентилем Адамара.'));
}

const out = ['@@FILE ' + REL2]; let n = 0;
for (const e of e2) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
fs.writeFileSync(path.join(__dirname, 'шаг-03-глава-VII2.txt'), out.join('\n') + '\n');
console.log('шаг-03-глава-VII2.txt: правок ' + n);
