// Собирает описание правок шага 4 Части IX («Навье–Стокс: нелинейность, которая переносит»; места 5.1, 5.2,
// 5.3): глава IX.5.
// Формализация — src/navier_stokes/GalerkinAdvection.v.
// «Было» берётся с живой страницы. Запуск: node make-step-04-spec.cjs [--keep-formula]
//   --keep-formula   вопрос 1 (развилка 1), вариант 2: формула антисимметрии B(k,l,m) = −B(k,m,l) на странице
//                    остаётся; рядом сказано, что при ней нелинейность вырождена, и названа вторая антисимметрия
// Итог: шаг-04-глава-IX5.txt. L() превращает «¤» в обратную косую черту.
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/09 Уравнения в частных производных/';
const REL5 = DIR + '05 Навье–Стокс и синтез.md';
const BS = String.fromCharCode(92);
const L = (s) => s.split('¤').join(BS);   // «¤» — обратная косая черта
const KEEP_FORMULA = process.argv.includes('--keep-formula');

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

const FN2_V1 = L('[^2]: `adv_antisym` в `GalerkinAdvection.v` — лемма: `adv T k l m := T k l m - T m l k`, `T` — произвольная сырая связь; аксиом и посылок нет. Теорема `adv_energy_zero` формализует, что конвекция *сохраняет* энергию (лишь перебрасывает её между модами), не создавая и не уничтожая — дискретный аналог того, что $¤int (u¤cdot¤nabla u)¤cdot u = 0$; перенос при этом ненулевой: на двух модах система имеет вид $da_0/dt=a_0a_1$, $da_1/dt=-a_0^2$ (`adv_pair_nl`). Прежний коэффициент `B_coeff` (`GalerkinSystem.v`) антисимметричен по двум последним индексам, $B(k,l,m)=-B(k,m,l)$ (`B_antisym`); при такой антисимметрии нелинейный член каждой моды равен нулю (`nl_mode_zero`), и правая часть системы совпадает с вязкой (`grhs_formal_is_viscous`). Сеточная форма сохранения — `burgers_conserves_energy` (`AdvectionEnergyConservation.v`).');
const FN2_V2 = L('[^2]: `B_antisym` в `GalerkinSystem.v` — лемма: `B_coeff k l m := B_raw k l m - B_raw k m l`, `B_raw` — поле записи посылок; аксиом в файле нет. Нелинейный член каждой моды с этим коэффициентом равен нулю (`nl_mode_zero`, `GalerkinAdvection.v`), и правая часть системы совпадает с вязкой (`grhs_formal_is_viscous`). Сохранение энергии при ненулевом переносе — `adv_energy_zero` для `adv T k l m := T k l m - T m l k` (там же): конвекция лишь перебрасывает энергию между модами, не создавая и не уничтожая, — дискретный аналог того, что $¤int (u¤cdot¤nabla u)¤cdot u = 0$; на двух модах система имеет вид $da_0/dt=a_0a_1$, $da_1/dt=-a_0^2$ (`adv_pair_nl`). Сеточная форма сохранения — `burgers_conserves_energy` (`AdvectionEnergyConservation.v`).');
const FN7 = L('[^7]: Правая часть системы, шаг явной схемы и состояние после $n$ шагов — `grhs`, `gstep`, `gtraj` в `GalerkinAdvection.v` (`navier_stokes/`); нелинейный член моды — `nl`. Правило отбора триад, давление и условие несжимаемости не формализованы.');

const e5 = [];
{
  const { old, inline } = loader(REL5);

  // 1. места 5.2 и 5.1 (вопрос 1; стр. 58–62): система и антисимметрия
  if (!KEEP_FORMULA) e5.push({ old: old('*триадным* взаимодействием $B(k,l,m)$ между модами. Ключевое свойство нелинейности —', 'антисимметрия коэффициента, $B(k,l,m) = -B(k,m,l)$; в формализации это лемма: коэффициент'),
    neu: ['*триадным* взаимодействием $B(k,l,m)$ между модами.[^7] Ключевое свойство нелинейности —',
          'антисимметрия коэффициента по проверяемой и переносимой модам, $B(k,l,m) = -B(m,l,k)$; в',
          'формализации это лемма: коэффициент'] });
  else e5.push({ old: old('*триадным* взаимодействием $B(k,l,m)$ между модами. Ключевое свойство нелинейности —', 'единственный сток энергии — вязкая диффузия.'),
    neu: ['*триадным* взаимодействием $B(k,l,m)$ между модами.[^7] Ключевое свойство нелинейности —',
          'антисимметрия коэффициента, $B(k,l,m) = -B(k,m,l)$; в формализации это лемма: коэффициент',
          'задан как антисимметризация абстрактной связи.[^2] При такой антисимметрии нелинейный член',
          'каждой моды равен нулю: в формальном слое нелинейность вырождена. Энергию при ненулевом',
          'переносе сохраняет антисимметрия по проверяемой и переносимой модам, $B(k,l,m) = -B(m,l,k)$:',
          'тогда нелинейность энергию только *перераспределяет*, как линейный перенос перераспределял',
          'массу (Глава 9.4), и единственный сток энергии — вязкая диффузия.'] });

  // 2. место 5.3 (стр. 78–79): тождество скорости энергии
  e5.push({ old: old('В модальном (галёркинском) слое это записано как эволюционное тождество для скорости', 'энергии (`energy_rate_formula`, над рациональными процессами); классическая запись'),
    neu: ['В модальном (галёркинском) слое это записано как тождество для скорости энергии вдоль',
          L('правой части системы, $¤sum_k a_k F_k(a) = -2¤nu¤Omega$ (`galerkin_energy_rate`, над'),
          'рациональными амплитудами), и как точное тождество шага схемы,',
          L('$E(a^{n+1}) = E(a^n) - 2¤nu¤,¤Delta t¤,¤Omega + ¤tfrac12 ¤Delta t^2 ¤sum_k F_k^2$'),
          '(`galerkin_step_energy`); классическая запись'] });

  // 3. место 5.2 (стр. 127): схема шага «на всех уровнях»
  e5.push(inline(L('схема $u^{n+1}=u^n+¤Delta t ¤mathcal L_h u^n$ и конечные законы'),
    L('¤mathcal L_h u^n$ и конечные законы'),
    L('¤mathcal L_h u^n$ (для волны — двухслойная, для Навье–Стокса — на амплитудах мод) и конечные законы')));

  // 4. сноска 1: новый файл
  e5.push(inline('[^1]:', ' Точные имена и счётчики',
    ' Система амплитуд с переносящей нелинейностью, её шаг и траектория — `GalerkinAdvection.v` (23 утверждения, 0 аксиом; теоремы о новой системе записи посылок не берут). Точные имена и счётчики'));

  // 5. сноска 2 (место 5.1, вопрос 1)
  { const o = old('[^2]:', '[^2]:'); e5.push({ old: o, neu: [KEEP_FORMULA ? FN2_V2 : FN2_V1] }); }

  // 6. сноска 3 (место 5.3): первая половина
  e5.push(inline('[^3]:',
    L('`energy_rate_formula` (`GalerkinSystem.v`: $dE/dt=-2¤nu¤Omega$; нелинейный вклад нулевой — `nonlinear_energy_zero`) и `energy_bounded_by_initial`'),
    L('`galerkin_energy_rate` и `galerkin_step_energy` (`GalerkinAdvection.v`): скорость энергии выведена из правой части системы, нелинейный вклад нулевой — `adv_energy_zero`. В `GalerkinSystem.v` то же тождество записано для состояния — `energy_rate_formula`: вязкий вклад $-2¤nu¤Omega$ взят там по определению, нелинейный вклад — `nonlinear_energy_zero`. Далее — `energy_bounded_by_initial`')));

  // 7. новая сноска 7 (место 5.2)
  { const o = old('[^6]:', '[^6]:'); e5.push({ old: o, neu: [o[0], FN7] }); }
}

const out = []; let n = 0;
out.push('@@FILE ' + REL5); for (const e of e5) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
fs.writeFileSync(path.join(__dirname, 'шаг-04-глава-IX5.txt'), out.join('\n') + '\n');
console.log('шаг-04-глава-IX5.txt: правок ' + n + (KEEP_FORMULA ? ' [формула антисимметрии страницы оставлена]' : ''));
