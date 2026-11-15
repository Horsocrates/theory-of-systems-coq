// Собирает описание правок шага 6 Части VI («операторы I: лестница осциллятора»; места 6.1–6.3):
// 4 правки главы VI.6. Формализация — src/process/ProcessLadderRational.v. «Было» берётся с живой страницы.
// Запуск: node make-step-06-spec.cjs  -> шаг-06-глава-VI6.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/06 Меры и интегрирование/';
const REL6 = DIR + '06 Операторы на L^2 самосопряжённость, спектр и мост в квантовую динамику.md';
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

const e6 = [];
{
  const { old, inline, whole } = loader(REL6);
  // 1. место 6.2: гамильтониан через лестницу
  e6.push(inline(L('Оператор числа $N=a^§dagger a$ считает кванты, а гамильтониан осциллятора имеет спектр,'),
    'а гамильтониан осциллятора имеет спектр,', L('а гамильтониан осциллятора $H=a^§dagger a+§tfrac12$ имеет спектр,')));
  // 2. места 6.1, 6.3: усечения и рациональные веса вместо параметра s
  e6.push({ old: old('Пространство состояний осциллятора — *пространство Фока* — удерживается процессно: как',
                     L('уровнях, шаге, коммутаторе — $§sqrt{§;}$ сокращается, оставляя рациональные величины.')),
    neu: ['Пространство состояний осциллятора — *пространство Фока* — удерживается процессно: как',
          'процесс конечных усечений (первые $K$ уровней), актуальных на каждой стадии. На усечении',
          'коммутатор равен единице на всех уровнях ниже верхнего, а на верхнем уровне равен $-(K-1)$:',
          'дефект усечения сидит на его краю и с ростом $K$ уходит вверх. Иррациональный множитель',
          L('$§sqrt n$, входящий в привычную запись лестничных операторов, в ToS не вводится: над ℚ'),
          L('числа $s$ с $s^2=2$ нет. Его место занимают два рациональных веса с произведением'),
          L('$§alpha_n§beta_n=n$ — понижение умножает на $§alpha_n$, повышение на $§beta_n$; простейший'),
          L('выбор — $§alpha_n=n$, $§beta_n=1$. Это запись в ненормированных состояниях,'),
          L('$§langle n|n§rangle=n!$: в скалярном произведении с весами $n!$ операторы $a$ и $a^§dagger$'),
          'взаимно сопряжены. Лестничная алгебра от выбора весов не зависит, и в наблюдаемых —',
          'уровнях, шаге, коммутаторе — стоят одни рациональные величины.'] });
  // 3. сноска 1: перечень файлов
  e6.push(inline('[^1]: Опорные файлы каталога `src/process/`:',
    '`ProcessHarmonicLadder.v`, `ProcessCanonicalCommutator.v`', '`ProcessHarmonicLadder.v`, `ProcessLadderRational.v`, `ProcessCanonicalCommutator.v`'));
  // 4. места 6.1–6.3: сноска 9
  e6.push(whole(L('[^9]: `commutator_canonical` ($[a,a^§dagger]=1$), `cre_ann_eq_num`'),
    L('[^9]: Лестница с рациональными весами — файл `ProcessLadderRational.v` (0 аксиом): `commutator_canonical_rational` ($[a,a^§dagger]=1$), `number_operator_rational` ($N=a^§dagger a$), `ham_rational_eigen` ($(a^§dagger a+§tfrac12)|n§rangle=(n+§tfrac12)|n§rangle$ — формула уровней как следствие лестницы), `ladder_adjoint_factorial` (сопряжённость $a$ и $a^§dagger$ с весами $n!$); для любых весов с $§alpha_n§beta_n=n$ — `gcommutator_canonical`, `gham_from_ladder`. Усечения: `truncated_commutator_below_top` и `truncated_commutator_top`. Свойства формулы уровней — `energy_spacing` (шаг $1$), `ground_energy` ($§tfrac12$) и `energy_unbounded` (спектр неограничен) в `ProcessHarmonicLadder.v` (0 аксиом). Прежние `commutator_canonical` и `cre_ann_eq_num` того же файла стоят под посылкой «рациональное $s$ с $s(n)^2=n$ при всех $n$», а такого $s$ нет (`ladder_premise_unsatisfiable`).')));
}

const out = ['@@FILE ' + REL6]; let n = 0;
for (const e of e6) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
fs.writeFileSync(path.join(__dirname, 'шаг-06-глава-VI6.txt'), out.join('\n') + '\n');
console.log('шаг-06-глава-VI6.txt: правок ' + n);
