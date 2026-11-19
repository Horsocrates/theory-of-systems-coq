// Собирает описание правок шага 2 Части VII («Ортогональные системы без корня и система Уолша»; места 1.3, 1.4,
// 2.2, а также число в сноске 1 главы VII.2 — место 2.3): 5 правок главы VII.1 и 5 правок главы VII.2.
// Формализация — src/process/ProcessOrthogonalWalsh.v. «Было» берётся с живой страницы.
// Запуск: node make-step-02-spec.cjs  -> шаг-02-главы-VII1-и-VII2.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/07 Гармонический анализ/';
const REL1 = DIR + '01 Ортонормированные системы и коэффициенты Фурье.md';
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
  const after = (prefix, add) => { const o = old(prefix, prefix); return { old: o, neu: [o[0], add] }; };
  return { old, inline, after };
}

// ---------- Глава VII.1 ----------
const e1 = [];
{
  const { old, inline, after } = loader(REL1);
  // 1. место 1.3: «не вводит нормировку иначе как абстрактным параметром»
  e1.push({ old: old('пространство, и не вводит нормировку', '(она иррациональна'),
    neu: [L('пространство, и не извлекает корень $§sqrt N$: нормировка $1/§sqrt N$ рациональна лишь'),
          'когда $N$ — точный квадрат, а в остальных случаях теория ведётся для ортогональной',
          'системы без нормировки (§ «Конкретная ортогональная система: Уолш–Адамар»).'] });
  // 2. место 1.3: нормировка Уолша — чётные k, нечётные k, теория без корня
  e1.push({ old: old(L('нужно нормировать: $e_k = H_k/§sqrt N$. И вот здесь'), 'параметризуется, а в наблюдаемых величинах сокращается).'),
    neu: [L('нужно нормировать: $e_k = H_k/§sqrt N$. И вот здесь — единственная иррациональность: множитель $1/§sqrt N$ рационален лишь когда $N$ — точный'),
          L('квадрат, то есть при чётном $k$ ($N=4^j$, $§sqrt N=2^j$; например $N=4$, $§sqrt N=2$): тогда нормированные'),
          'строки удовлетворяют `Hon`, и это доказано. При нечётном $k$ рационального $s$ с $s^2=N$',
          'нет — это тоже доказано,— и корень не вводится вовсе: вся теория главы пересказана для',
          L('*ортогональной* системы с квадратами норм $d_k$ (коэффициент $c_k=§inner{e_k}{f}/d_k$), так что'),
          L('в наблюдаемых величинах стоит $N$, а не $§sqrt N$,— в согласии с приёмом Части VI (корень в'),
          'наблюдаемых величинах сокращается).[^17]'] });
  // 3. место 1.3: Парсеваль в делённой форме — при всяком k
  e1.push({ old: old('Переход к нормированной системе делит обе части на $N$ и возвращает Парсеваль в', L('форме $§sum_k c_k^2')),
    neu: [L('Деление обеих частей на $N$ возвращает Парсеваль в форме $§sum_k c_k^2 = §norm{f}^2$ с'),
          L('$c_k^2=§inner{H_k}{f}^2/N$ — при всяком $k$ и без корня.')] });
  // 4. место 1.4: анонс главы VII.2 — система ортогональна
  e1.push(inline('Следующая глава предъявляет конкретную рациональную ортонормированную систему во',
    'рациональную ортонормированную систему', 'рациональную ортогональную систему'));
  // 5. новая сноска 17
  e1.push(after('[^16]: Шапки дают разметку прямо:',
    L('[^17]: Файл `ProcessOrthogonalWalsh.v` (32 утверждения, 0 аксиом). Ортогональная система с квадратами норм $d_k>0$, $K§le K_0$: тождество остатка `resid_norm_og`, ортогональность остатка `resid_ortho_og`, Бессель `bessel_og` ($§sum_{k<K}§inner{e_k}{f}^2/d_k§le§norm{f}^2$), наилучшее приближение `best_approx_eq_og` с единственностью `best_approx_unique_og`, критерий полноты `parseval_iff_complete_og`. Для строк Уолша при всяком $N=2^k$ ($d_k=N$): `walsh_bessel`, `walsh_best_approx`, `walsh_parseval_divided` ($§sum_{i<N}§inner{H_i}{f}^2/N=§norm{f}^2$), `walsh_complete` ($f(m)=§sum_{i<N}(§inner{H_i}{f}/N)§,H_i(m)$). Нормировка: рациональное $s$ с $s^2=2^k$ существует тогда и только тогда, когда $k$ чётно, — `walsh_rational_norm_iff_even`; при $N=4^j$ строки, делённые на $2^j$, удовлетворяют `Hon` — `walsh_4j_orthonormal`; при нечётном $k$ такого $s$ нет — `walsh_odd_no_rational_norm`.')));
}

// ---------- Глава VII.2 ----------
const e2 = [];
{
  const { old, inline, after } = loader(REL2);
  // 1. место 1.3 (в главе VII.2): нормировка — в точности при чётном k
  e2.push({ old: old('$N$ — точный квадрат (для $N=2^k$ — лишь при чётном $k$); поэтому нормировка',
                     'вводится абстрактным параметром, а не вычисляется. Комплексный DFT (корни единицы'),
    neu: ['$N$ — точный квадрат (для $N=2^k$ — в точности при чётном $k$, и это доказано); поэтому при',
          'нечётном $k$ над ℚ нормировки нет, и теория ведётся для ортогональной системы с квадратом',
          'нормы $N$. Комплексный DFT (корни единицы'] });
  // 2. место 2.2: теория Главы 7.1 на системе Уолша — в ортогональной форме
  e2.push({ old: old('система, на которой буквально выполняется вся абстрактная теория Главы 7.1',
                     L('$§inner{e_i}{e_j}=N§delta_{ij}$ — не постулат, а доказанное равенство.')),
    neu: ['система, на которой выполняется вся абстрактная теория Главы 7.1 в ортогональной форме —',
          'с квадратом нормы $N$ на месте единицы (коэффициенты, проекция, Бессель, Парсеваль),—',
          'причём каждая её предпосылка —',
          L('$§inner{e_i}{e_j}=N§delta_{ij}$ — не постулат, а доказанное равенство.[^11]')] });
  // 3. место 2.3 и новый файл: сноска 1
  e2.push(inline('[^1]: Опорный файл — `ProcessWalshHadamard.v`',
    '`ProcessWalshCharacter.v` (7 утверждений) и `ProcessHadamardGate.v` (5 утверждений).',
    '`ProcessWalshCharacter.v` (8 утверждений), `ProcessHadamardGate.v` (5 утверждений) и `ProcessOrthogonalWalsh.v` (32 утверждения).'));
  // 4. сноска 4: разные строки — разные функции
  e2.push(inline('[^4]: Теорема `had_character` в `ProcessWalshCharacter.v`',
    'XOR здесь — операция группы $ℤ_2^{ n}$.',
    L('XOR здесь — операция группы $ℤ_2^{ n}$. Разные строки — разные функции на $§{0,§dots,N-1§}$: `walsh_rows_distinct` (`ProcessOrthogonalWalsh.v`, 0 аксиом).')));
  // 5. новая сноска 11
  e2.push(after('[^10]: Шапки дают разметку прямо:',
    L('[^11]: Теория Главы 7.1 в ортогональной форме (квадраты норм $d_k$ на месте единиц, коэффициент $c_k=§inner{e_k}{f}/d_k$) — файл `ProcessOrthogonalWalsh.v` (32 утверждения, 0 аксиом): `resid_ortho_og`, `resid_norm_og`, `bessel_og`, `best_approx_og`, `best_approx_unique_og`, `parseval_iff_complete_og`. К строкам Уолша она применена при всяком $N=2^k$ с $d_k=N$ (`walsh_og`): `walsh_bessel` ($§sum_{i<K}(Hf)_i^2/N§le§norm{f}^2$), `walsh_best_approx`, `walsh_parseval_divided`, `walsh_complete` ($f(m)=§sum_{i<N}§frac{(Hf)_i}{N}§,H_{im}$); коэффициент $§inner{H_i}{f}$ есть $i$-я координата преобразования — `walsh_coef_is_transform`. Нормировка: рациональное $s$ с $s^2=2^k$ существует тогда и только тогда, когда $k$ чётно (`walsh_rational_norm_iff_even`); при $N=4^j$ строки, делённые на $2^j$, ортонормированы (`walsh_4j_orthonormal`), и к ним применимы теоремы Главы 7.1 в исходной форме (`walsh_normalized_bessel`, `walsh_normalized_parseval`, `walsh_normalized_complete`).')));
}

const out = []; let n = 0;
for (const [rel, es] of [[REL1, e1], [REL2, e2]]) {
  out.push('@@FILE ' + rel);
  for (const e of es) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
}
fs.writeFileSync(path.join(__dirname, 'шаг-02-главы-VII1-и-VII2.txt'), out.join('\n') + '\n');
console.log('шаг-02-главы-VII1-и-VII2.txt: правок ' + n + ' (VII.1 — ' + e1.length + ', VII.2 — ' + e2.length + ')');
