// Собирает описание правок шага 4 Части VIII («Гронуолл и устойчивость»; места 4.1–4.5): глава VIII.4.
// Формализация — src/process/ProcessGronwallInequality.v (и файлы шагов 1–2: ProcessExpLadder.v,
// ProcessPicardGridSolution.v).
// «Было» берётся с живой страницы. Запуск: node make-step-04-spec.cjs [--no-l3] [--keep-regimes] [--keep-tense]
//   --no-l3         вопрос 1, вариант 2: в разборе (стр. 190–192) слово L3 не остаётся вовсе
//   --keep-regimes  вопрос 2, вариант 2: курсив о двух режимах (стр. 143–144) не трогается
//   --keep-tense    вопрос 3, вариант 2: «разбирался в Главах 8.2 и 8.5» (стр. 158) не трогается
// Итог: шаг-04-глава-VIII4.txt. L() превращает «¤» в обратную косую черту; знак параграфа пишется прямо.
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/08 Обыкновенные дифференциальные уравнения/';
const REL4 = DIR + '04 Устойчивость, единственность, неравенство Гронуолла.md';
const BS = String.fromCharCode(92);
const L = (s) => s.split('¤').join(BS);   // «¤» — обратная косая черта
const NO_L3 = process.argv.includes('--no-l3');
const KEEP_REG = process.argv.includes('--keep-regimes');
const KEEP_TENSE = process.argv.includes('--keep-tense');

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

const e4 = [];
{
  const { old, inline, whole } = loader(REL4);

  // 1. место 4.5 (стр. 9–10): пересказ Главы 8.3
  e4.push({ old: old('Глава 8.3 дала гарантию: при липшицевости правой части оператор Пикара сжимает, а', 'значит, процесс приближений сходится и решение единственно. Но у задачи Коши есть'),
    neu: ['Глава 8.3 дала гарантию: при липшицевости правой части на достаточно коротком отрезке',
          '($LT<1$) оператор Пикара сжимает, и его итерации сближаются геометрически; а на сетке',
          'решение существует и единственно при любой длине отрезка. Но у задачи Коши есть'] });

  // 2. место 4.3 (стр. 31–33): цена ε-сходимости множителя
  e4.push({ old: old('проверен `Print Assumptions`; переход к', 'завершённому $e^{Lt}$ относится к L3-слою (как в Главе 8.3).'),
    neu: [L('проверен `Print Assumptions`; без аксиом доказана и $¤varepsilon$-сходимость множителя —'),
          'свойство Коши лестницы $(1+Lt/n)^n$; завершённый $e^{Lt}$ как объект формальный слой не',
          'строит.'] });

  // 3. место 4.3 (стр. 38–39)
  e4.push(whole(L('$¤varepsilon$-сходимость к нему наследует L3 (как и в Главе 8.3).'),
    L('$¤varepsilon$-сходимость есть свойство Коши самого процесса и аксиом не требует.')));

  // 4. место 4.4 (стр. 137–139): затухание
  e4.push(whole(L('не растёт, а *убывает*: $u_n ¤le u_0$.[^7]'),
    L('с неотрицательным началом $u_0 ¤ge 0$ не растёт, а *убывает*: $u_{n+1} ¤le u_n ¤le u_0$.[^7]')));

  // 5. вопрос 2 (стр. 143–144): курсив о двух режимах
  if (!KEEP_REG) e4.push(whole(L('два его режима ($¤alpha$ положительно или отрицательно.)*'),
    L('два его режима ($¤alpha$ положительно — или отрицательно при $¤lvert¤alpha¤rvert h ¤le 1$.)*')));

  // 6. вопрос 3 (стр. 158): где разбирается e-процесс
  if (!KEEP_TENSE) e4.push(inline('$e$-процесса, что разбирался в Главах 8.2 и 8.5.[^8]',
    '$e$-процесса, что разбирался в Главах 8.2 и 8.5.[^8]',
    '$e$-процесса, что разбирался в Главе 8.2 и разбирается в Главе 8.5.[^8]'));

  // 7. места 4.1–4.3 (стр. 162–166): что доказано
  e4.push({ old: old('совпадение с однородным Гронуоллом, тождество множителя со стадией', 'Главе 8.3).'),
    neu: ['совпадение с однородным Гронуоллом, тождество множителя со стадией $e^{Lt}$-процесса,',
          'оценка расхождения в момент $t$ числом, не зависящим от числа шагов, и',
          L('$¤varepsilon$-сходимость самой лестницы множителей. Завершённый $e^{Lt}$ и безусловная'),
          'оценка на бесконечном интервале — роль-предел и граница: в формальном слое их нет.'] });

  // 8. места 4.2, 4.3 (стр. 189–192): Rules разбора; вопрос 1
  e4.push({ old: old(L('затухание при множителе $¤le 1$). Венчает — тождество множителя $(1+Lt/n)^n$ со'), 'его не требуют.'),
    neu: [L('затухание при множителе $¤le 1$). Венчает — тождество множителя $(1+Lt/n)^n$ со'),
          'стадией $e^{Lt}$-процесса и оценка расхождения в момент $t$ этой стадией: лестница стадий']
      .concat(NO_L3
        ? [L('не убывает, ограничена и образует процесс Коши. Ни рациональные оценки, ни'),
           L('$¤varepsilon$-сходимость множителя L3 не требуют; завершённого $e^{Lt}$ формальный слой'),
           'не строит.']
        : ['не убывает, ограничена и образует процесс Коши. Универсальный слой L3 в доказанное не',
           L('входит: ни рациональные оценки, ни $¤varepsilon$-сходимость множителя его не требуют; к L3'),
           'относится лишь актуализация $e^{Lt}$ как завершённого объекта (Глава 8.1, § «Где',
           'появляется граница»), и в формальном слое её нет.']) });

  // 9. сноска 1: новые опорные файлы
  e4.push(inline('[^1]:',
    '). Единственность — `picard_unique` (`ProcessPicardOperator.v`, Глава 8.3).',
    '), а также `ProcessGronwallInequality.v` (неравенство Гронуолла для произвольной последовательности, оценка расхождения как его случай, оценки в момент $t$, затухание; 0 аксиом) и `ProcessExpLadder.v` (лестница $(1+s/n)^n$: рост, ограниченность, свойство Коши; 0 аксиом). Единственность — `picard_unique` (`ProcessPicardOperator.v`, Глава 8.3).'));

  // 10. сноска 2: условие LT < 1; единственность как нулевое возмущение — теоремами
  e4.push(whole('[^2]:',
    L('[^2]: `picard_unique` в `ProcessPicardOperator.v`: при $LT<1$, если две грид-функции неподвижны под оператором Пикара, они совпадают во всех узлах сетки; без условия на $LT$ — `picard_unique_any_rate` (`ProcessPicardGridSolution.v`). Прочтение «единственность есть устойчивость при нулевом возмущении» записано теоремами в `ProcessGronwallInequality.v`: две неподвижные точки с началами $y_0$ и $¤tilde y_0$ расходятся в узле $k$ не более чем в $(1+Lh)^k$ раз от $¤lvert y_0 - ¤tilde y_0¤rvert$ (`picard_fixed_stability`), при равных началах они совпадают (`picard_unique_as_zero_perturbation`); для самих ломаных Эйлера — `euler_same_start`. 0 аксиом (Глава 8.3).')));

  // 11. сноска 4: точность оценки; форма «для всякого ε найдётся δ»
  e4.push(inline('[^4]:',
    'индукцией по $n$ через `euler_step_diff`. 0 аксиом.',
    L('индукцией по $n$ через `euler_step_diff`. 0 аксиом. Оценка точна: для $f(t,y) = Ly$ в ней стоит равенство (`euler_diff_bound_sharp`). «Малое возмущение даёт малое расхождение» в форме «для всякого $¤varepsilon$ найдётся $¤delta$» — `euler_continuous_dependence` (на данном шаге) и `euler_continuous_dependence_uniform` (в момент $t$: одно $¤delta$ для всякого числа шагов) в `ProcessGronwallInequality.v`. 0 аксиом.')));

  // 12. сноска 6 (место 4.1): само неравенство и оценка расхождения как его случай
  e4.push(inline('[^6]:',
    L('При $¤alpha=L$ это правая часть `euler_diff_bound`.'),
    L('При $¤alpha=L$ это правая часть `euler_diff_bound` (`euler_bound_is_gronwall_iterate`). Само неравенство — для всякой последовательности, растущей не быстрее шага, при неотрицательном множителе $1+¤alpha h$ — `gronwall_inequality` (однородный случай — `gronwall_inequality_hom`, с притоком в явном виде — `gronwall_inequality_forced`); оценка расхождения как его случай — `euler_divergence_gronwall`. Все — в `ProcessGronwallInequality.v`, 0 аксиом.')));

  // 13. сноска 7 (место 4.4): условие u0 >= 0; затухание по модулю
  e4.push(whole('[^7]:',
    L('[^7]: `gronwall_decay_factor` в `ProcessGronwall.v`: для $0 ¤le r ¤le 1$ и $u_0 ¤ge 0$ выполнено $u_0 r^n ¤le u_0$; без условия $u_0 ¤ge 0$ это неверно (`decay_factor_needs_u0_nonneg`). Для самой итерации — `gronwall_iterate_decay` ($u_n ¤le u_0$) и `gronwall_iterate_decay_monotone` ($u_{n+1} ¤le u_n$) в `ProcessGronwallInequality.v`. При начале любого знака убывает модуль: если $¤lvert r¤rvert ¤le 1$, то $¤lvert u_{n+1}¤rvert ¤le ¤lvert u_n¤rvert ¤le ¤lvert u_0¤rvert$ (`gronwall_iterate_abs_monotone`, `gronwall_iterate_abs_decay`), а при $¤lvert r¤rvert < 1$ итерация стремится к нулю (`gronwall_iterate_vanishes`). 0 аксиом.')));

  // 14. сноска 8 (места 4.2, 4.3): что даёт тождеству содержание
  e4.push(inline('[^8]:',
    ' (батч C). 0 аксиом. При $s = Lt$ это $(1+Lt/n)^n$.',
    L(' — по определению этого процесса. 0 аксиом. При $s = Lt$ это $(1+Lt/n)^n$. Содержание тождеству дают теоремы: подстановка шага $h = t/n$ в оценку расхождения — `euler_divergence_expt` (`ProcessGronwallInequality.v`): расхождение в момент $t$ не больше стадии лестницы, умноженной на $¤lvert¤Delta_0¤rvert$; стадии не убывают (`expt_monotone`) и ограничены числом, одним для всех (`expt_bounded`; оба — `ProcessExpLadder.v`), так что расхождение в момент $t$ оценено независимо от числа шагов (`euler_divergence_uniform`); лестница множителей — процесс Коши с явным модулем (`expt_process_is_Cauchy`, `expt_modulus`); при $s = 1$ она совпадает с $e$-процессом (`expt_at_one`). 0 аксиом.')));
}

const out = ['@@FILE ' + REL4]; let n = 0;
for (const e of e4) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
fs.writeFileSync(path.join(__dirname, 'шаг-04-глава-VIII4.txt'), out.join('\n') + '\n');
console.log('шаг-04-глава-VIII4.txt: правок ' + n + (NO_L3 ? ' [без слова L3]' : '') + (KEEP_REG ? ' [курсив о режимах оставлен]' : '') + (KEEP_TENSE ? ' [стр. 158 оставлена]' : ''));
