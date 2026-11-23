// Собирает описание правок шага 1 Части VIII («Метод Эйлера в общем виде и лестница e»; места 2.1–2.4):
// 8 правок главы VIII.2. Формализация — src/analysis/EulerTrajectoryGeneral.v и src/process/ProcessExpLadder.v.
// «Было» берётся с живой страницы. Запуск: node make-step-01-spec.cjs -> шаг-01-глава-VIII2.txt
// Внимание: строки с настоящим знаком параграфа через L() не пропускать.
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/08 Обыкновенные дифференциальные уравнения/';
const REL2 = DIR + '02 Метод Эйлера решение на сетке.md';
const BS = String.fromCharCode(92);
const L = (s) => s.split('§').join(BS);   // «§» в строках, идущих через L(), — обратная косая черта

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
  // 1. место 2.3: ошибка для y' = 2t на всякой сетке
  e2.push({ old: old('нулю». Метод недооценивает решение', 'мера этого отставания на каждой конкретной сетке вычислена точно. Уменьшение'),
    neu: ['нулю». Метод недооценивает решение (выпуклая кривая обгоняет свои касательные), и',
          'мера этого отставания на каждой конкретной сетке вычислена точно: в момент $t = 1$',
          'ошибка равна шагу сетки, $1/N$. Уменьшение'] });
  // 2. место 2.1: лестница (1+1/N)^N — оценки, рост и сближение стадий для всех N
  e2.push({ old: old('Это в точности тот же приём, что для $e$-процесса', 'строится.'),
    neu: ["Это в точности тот же приём, что для $e$-процесса как решения $y' = y$ (Глава 8.5):",
          'тамошняя последовательность $(1+1/(N{+}1))^{N+1}$ — та же лестница рациональных',
          "стадий, и доказано, что она *есть* траектория Эйлера уравнения $y' = y$ при",
          '$t = 1$, ограничена снизу двойкой (по неравенству Бернулли) и сверху тройкой и растёт',
          'на каждой стадии — всё это *для всех* $N$; доказано и то, что стадии сближаются: при',
          'разрешениях не меньше $N_0$ любые две стадии $(1+1/N)^N$ различаются меньше чем на',
          '$3/N_0$.[^9] Честная граница данного слоя — завершённый предел: явное число $e$ как',
          'завершённая трансцендентность — роль-предел. Доказано конкретное: рациональные стадии,',
          L('оценки $2 §le (1+1/N)^N < 3$, рост и сближение стадий для всех $N$; завершённое $e$ не'),
          'строится.'] });
  // 3. сноска 1: опорные файлы
  e2.push(whole('[^1]: Опорный файл',
    '[^1]: Опорные файлы (Rocq-репозиторий ToS). `analysis/PicardLindelof.v`: `grid`, `euler_step`, `euler_traj` и теоремы о конкретных траекториях (`euler_traj_linear_4`, `euler_quadratic_error`, `euler_traj_exp_4` и др.) — точная рациональная арифметика (`vm_compute`, `field` или `ring`). `analysis/EulerTrajectoryGeneral.v`: те же три траектории в общем виде — на всякой сетке и во всяком узле (`euler_traj_const_exact`, `euler_traj_quadratic_closed`, `euler_traj_exp_closed`). Для экспоненты как процесса — `ProcessExpProcess.v` и `ProcessExpLadder.v` (Глава 8.5): оценки, рост и сближение стадий для всех $N$. Все — 0 аксиом (проверено `Print Assumptions`).'));
  // 4. сноска 5: место 2.2
  e2.push(inline('[^5]:', 'Точность — следствие отсутствия кривизны: правая часть постоянна.',
    L('Точность — следствие отсутствия кривизны: правая часть постоянна. В общем виде — `euler_traj_const_exact` в `EulerTrajectoryGeneral.v`: при всякой постоянной правой части $a$, всяком начальном значении, на всякой сетке и во всяком узле $y_k = y_0 + a§,t_k$.')));
  // 5. сноска 6: место 2.3
  e2.push(inline('[^6]:', 'Оба в `PicardLindelof.v`, точная арифметика.',
    'Оба в `PicardLindelof.v`, точная арифметика. В общем виде — в `EulerTrajectoryGeneral.v`: `euler_traj_quadratic_closed` ($y_k = t_k^2 - t_k h$ на всякой сетке, $h = 1/N$), `euler_quadratic_error_general` (в момент $t = 1$ ошибка равна $1/N$), `euler_quadratic_underestimates` (ошибка положительна) и `euler_quadratic_error_decreases` (с ростом $N$ она убывает).'));
  // 6. сноска 7: замкнутый вид траектории главы
  e2.push(inline('[^7]:', ' `lipschitz_identity`:',
    L(' Замкнутый вид всей траектории — `euler_traj_exp_closed` в `EulerTrajectoryGeneral.v`: $y_k = y_0§,(1+1/N)^k$ на всякой сетке. `lipschitz_identity`:')));
  // 7. сноска 9: место 2.1
  e2.push(whole('[^9]:',
    L("[^9]: `exp1_is_euler` (тождество «$e$-процесс${}={}$траектория Эйлера для $y'=y$ при $t=1$»), `exp1_lower` ($e$-процесс${}§ge 2$ *для всех* $N$, через Бернулли) и стадии $2, 9/4, 64/27$ (`exp1_0`, `_1`, `_2`) — в `ProcessExpProcess.v` (Глава 8.5). `exp1_upper` ($e$-процесс${}< 3$ *для всех* $N$), `exp1_increasing` (рост *для всех* $N$), `exp1_modulus` (за номером $N_0$ любые две стадии различаются меньше чем на $3/(N_0+1)$) и `exp1_is_Cauchy` (лестница — процесс Коши) — в `ProcessExpLadder.v`. Что та же лестница есть `euler_traj` этой главы при $k = N$ — `exp1_is_euler_traj` в `EulerTrajectoryGeneral.v`; там же оценки, рост и сближение стадий записаны для самой траектории (`euler_traj_exp_sandwich_all`, `euler_traj_exp_increasing`, `euler_exp_ladder_modulus`). Все — 0 аксиом (проверено `Print Assumptions`).")));
  // 8. сноска 10: место 2.4
  e2.push(whole('[^10]:',
    '[^10]: Шапка `PicardLindelof.v` даёт разметку прямо: Elements — правая часть $f$, узлы сетки $t_k$, значения траектории $y_k$; Roles — $f$ как векторное поле, $y_k$ как приближение, $h$ как размер шага; Rules — рекуррентность Эйлера $y_{k+1} = y_k + h f(t_k,y_k)$ и липшицево сжатие как оценка. Траектория как процесс (`nat -> Q`) названа там же, в строке о связи с P4.'));
}

const out = ['@@FILE ' + REL2]; let n = 0;
for (const e of e2) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
fs.writeFileSync(path.join(__dirname, 'шаг-01-глава-VIII2.txt'), out.join('\n') + '\n');
console.log('шаг-01-глава-VIII2.txt: правок ' + n);
