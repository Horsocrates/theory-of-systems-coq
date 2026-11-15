// Собирает описание правок шага 5 Части VI («L²»; места 5.1, 5.2, 5.4): 12 правок главы VI.5.
// Формализация — src/process/ProcessL2Orthonormal.v. «Было» берётся с живой страницы.
// Запуск: node make-step-05-spec.cjs  -> шаг-05-глава-VI5.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/06 Меры и интегрирование/';
const REL5 = DIR + '05 L^1 и L^2 пространства как процессы, полнота как конструируемость.md';
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

const e5 = [];
{
  const { old, inline, whole } = loader(REL5);
  // 1. место 5.1: определение ОН-системы и проекции
  e5.push({ old: old(L('*Ортонормированная* (ОН) система — семейство $§{e_k§}$ с'),
                     'при $i=j$ и $0$ иначе. *Проекция* функции $f$ на первые $K$ направлений — сумма'),
    neu: [L('*Ортонормированная* (ОН) система — конечное семейство $§{e_k§}_{k<K_0}$ с'),
          L('$§langle e_i,e_j§rangle=1$ при $i=j$ и $0$ иначе. *Проекция* функции $f$ на первые'),
          L('$K§le K_0$ направлений — сумма')] });
  // 2. место 5.1: оговорка в формуле Бесселя
  e5.push(inline(L('§sum_{k<K}c_k^2 §;§le§; §|f§|^2 §quad(§text{для любой ОН-системы и любого }K).'),
    L('§text{для любой ОН-системы и любого }K).'), L('§text{для любой ОН-системы и любого }K§le K_0).')));
  // 3. место 5.4: «определение RealProcess»
  e5.push(whole(L('определение вещественного как процесса (`RealProcess`, $ℕ§toℚ$). Значит, предел'),
    L('вещественное как процесс: `RealProcess` ($ℕ§toℚ$) с условием Коши `is_Cauchy`. Значит, предел')));
  // 4. сноска 1: перечень файлов
  e5.push(inline('[^1]: Опорные файлы каталога `src/process/` Rocq-репозитория ToS:',
    '`ProcessL2RieszFischer.v`; их связки', '`ProcessL2RieszFischer.v`, `ProcessL2Orthonormal.v`; их связки'));
  // 5. сноска 3: связь L1 и L2
  e5.push(inline('[^3]: Прямое следствие `q_sum_cauchy_schwarz`',
    L('с $g§equiv1$.'), L('с $g§equiv1$ — `l1_sq_le_N_l2_sq` (`ProcessL2Orthonormal.v`).')));
  // 6. место 5.2: сноска 4 — тождество Лагранжа
  e5.push(whole('[^4]: `q_sum_cauchy_schwarz` и `l2_cauchy_schwarz` в `ProcessL2CauchySchwarz.v` (0 аксиом);',
    '[^4]: `q_sum_cauchy_schwarz` и `l2_cauchy_schwarz` в `ProcessL2CauchySchwarz.v` (0 аксиом); опорные факты — неотрицательность квадрата `q_sq_nonneg` и разложение суммы квадратов `sos_identity`. Тождество Лагранжа — `lagrange_identity`, в виде формулы выше — `cs_gap_is_sum_of_squares`, неравенство из него — `cauchy_schwarz_via_lagrange` (`ProcessL2Orthonormal.v`, 0 аксиом).'));
  // 7. сноска 5: поляризация
  e5.push(inline('[^5]: Симметрия `l2_inner_sym` и разложение квадрата нормы `l2_inner_expand`',
    'поляризация — их прямое следствие.', 'поляризация — их прямое следствие (`l2_polarization`, `ProcessL2Orthonormal.v`).'));
  // 8. место 5.1: сноска 7 — ортогональность проекции
  e5.push(inline('[^7]: Линейность по разложению — `inner_proj_swap` в `ProcessL2BesselGeneral.v`',
    'ортогональность проекции — `proj_ortho`;', 'ортогональность проекции — `proj_ortho_b` (`ProcessL2Orthonormal.v`);'));
  // 9. сноска 8: одно направление
  e5.push(inline('[^8]: `pythagoras_one` и `bessel_one` в `ProcessL2Bessel.v` (0 аксиом).',
    '`pythagoras_one` и `bessel_one` в `ProcessL2Bessel.v` (0 аксиом).',
    '`pythagoras_one` и `bessel_one` в `ProcessL2Bessel.v` (0 аксиом); ортогональность остатка — `resid_ortho_one`, наименьшая норма остатка среди кратных $e$ — `best_approx_one` (`ProcessL2Orthonormal.v`, 0 аксиом).'));
  // 10. место 5.1: сноска 9 — Бессель и наилучшее приближение
  e5.push(whole('[^9]: `bessel_general` в `ProcessL2BesselGeneral.v` (0 аксиом):',
    L('[^9]: `bessel_b` в `ProcessL2Orthonormal.v` (0 аксиом): из тождества остатка `resid_norm_b` и неотрицательности суммы квадратов; посылка — ортонормированность первых $K_0$ векторов, $K§le K_0$. Наилучшее приближение — `best_approx_b`: проекция даёт наименьший остаток среди всех комбинаций первых $K$ векторов. Посылка выполнима: стандартный базис (`std_basis_on`) и повёрнутый рациональный базис $(3/5,4/5)$, $(-4/5,3/5)$ (`rot_orthonormal`). Прежние `bessel_general` и `resid_norm` (`ProcessL2BesselGeneral.v`) требуют ортонормированности при всех номерах $i,j$; на $N$ координатах такая посылка невыполнима (`on_all_indices_unsat`).')));
  // 11. место 5.1: сноска 10 — Парсеваль
  e5.push(whole('[^10]: `parseval_iff_complete` в `ProcessL2Parseval.v` (0 аксиом):',
    L('[^10]: `parseval_iff_complete_b` в `ProcessL2Orthonormal.v` (0 аксиом): `energy_split_b` $§sum c_k^2+§|r_K§|^2=§|f§|^2$, `parseval_iff_resid_zero_b`, и лемма `q_sum_sq_zero` из `ProcessL2Parseval.v` (сумма квадратов нулевая $§Rightarrow$ каждое слагаемое нулевое, через целостность умножения в ℚ). Равенство достигается на стандартном базисе при всяком $N$ и всякой $f$ — `parseval_std_all` — и на повёрнутом базисе — `parseval_rot`; частный свидетель — `parseval_std_concrete`.')));
  // 12. место 5.4: сноска 11 — координаты предела
  e5.push(inline('[^11]: `coord_sq_le_normsq`, `l2cauchy_coord_cauchy`, `l2_limit` и `l2_riesz_fischer`',
    'Конкретный свидетель — `const_l2cauchy`.',
    'Конкретный свидетель — `const_l2cauchy`. Что каждая координата предела есть процесс Коши (`is_Cauchy`) — `l2_limit_coord_is_Cauchy`; трёхчастная форма (координаты предела — процессы Коши; расстояние от $f_n$ до предела — процесс Коши; оно стремится к нулю) — `riesz_fischer_process_form` (`ProcessL2Orthonormal.v`, 0 аксиом).'));
}

const out = ['@@FILE ' + REL5]; let n = 0;
for (const e of e5) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
fs.writeFileSync(path.join(__dirname, 'шаг-05-глава-VI5.txt'), out.join('\n') + '\n');
console.log('шаг-05-глава-VI5.txt: правок ' + n);
