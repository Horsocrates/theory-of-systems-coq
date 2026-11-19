// Собирает описание правок шага 1 Части VII («Ортонормированные системы с выполнимой посылкой и ошибка ряда
// Фурье»; места 1.1, 1.2, 4.1, 4.3, 5.4): 15 правок главы VII.1 и 9 правок главы VII.4. Глава VII.5 (место 5.4)
// слов не меняет: её итоги становятся верными по новым теоремам.
// Формализация — src/process/ProcessOrthonormalFourier.v (поверх ProcessL2Orthonormal.v). «Было» берётся с живой страницы.
// Запуск: node make-step-01-spec.cjs  -> шаг-01-главы-VII1-и-VII4.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const DIR = 'Направления/Математика/Том Математика/07 Гармонический анализ/';
const REL1 = DIR + '01 Ортонормированные системы и коэффициенты Фурье.md';
const REL4 = DIR + '04 Сходимость рядов Фурье в L2.md';
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

// ---------- Глава VII.1 ----------
const e1 = [];
{
  const { old, inline, whole } = loader(REL1);
  // 1. место 1.1: условие на первые K0 векторов; их не больше N
  e1.push({ old: old('явно предъявленное условие на конкретный набор $e$, а не существование «какого-то', 'базиса».[^4] Система'),
    neu: [L('явно предъявленное условие на первые $K_0$ векторов конкретного набора $e$, а не'),
          L('существование «какого-то базиса».[^4] Таких векторов на $N$ координатах не больше $N$'),
          L('(доказано: $K_0§le N$), и всюду ниже $K§le K_0$. Система')] });
  // 2. место 1.1: Бессель — «любым числом K ≤ K0»
  e1.push(inline('Энергия, захваченная любым числом $K$ направлений, не превосходит полной энергии',
    'любым числом $K$ направлений', L('любым числом $K§le K_0$ направлений')));
  // 3. место 1.1: «Доказано конечное» — критерий и полнота N ортонормированных векторов
  e1.push(inline('базис.[^13] Доказано конечное: критерий полноты на $N$ координатах. Этого достаточно,',
    'Доказано конечное: критерий полноты на $N$ координатах. Этого достаточно,',
    'Доказано конечное: критерий полноты на $N$ координатах и полнота всякой системы из $N$ ортонормированных векторов — при $K=N$ разложение восстанавливает любую $f$. Этого достаточно,'));
  // 4. место 1.1: существуют ли системы, удовлетворяющие Hon
  e1.push({ old: old('*рациональная* система, на которой работает эта геометрия? Ответ требует одной',
                     'оговорки об уровне. Рациональная *ортогональная* система — да: её даёт'),
    neu: ['*рациональная* система, на которой работает эта геометрия? Простейшие предъявлены',
          'сразу: стандартный базис и повёрнутый рациональный базис $(3/5,4/5)$, $(-4/5,3/5)$',
          'удовлетворяют `Hon`. Для системы, несущей гармонический анализ, ответ требует одной',
          'оговорки об уровне. Рациональная *ортогональная* система — да: её даёт'] });
  // 5. сноска 1: опорные файлы
  e1.push(whole('[^1]: Опорные файлы — `ProcessL2BesselGeneral.v`',
    L('[^1]: Опорные файлы (каталог `src/process/` Rocq-репозитория ToS) — `ProcessL2Orthonormal.v` (36 доказанных утверждений) и `ProcessOrthonormalFourier.v` (30); оба — 0 `Admitted`, 0 аксиом. В них условие ортонормированности наложено на первые $K_0$ векторов системы, а теоремы доказаны для $K§le K_0$. Вспомогательные леммы о скалярном произведении — из `ProcessL2BesselGeneral.v` и `ProcessL2Parseval.v`. Имена лемм в сносках ниже — из этих файлов и из `ProcessFourierON.v`.')));
  // 6. сноска 3: билинейность в общем виде
  e1.push(whole('[^3]: `seq_inner_sym` (симметрия) и `seq_inner_sub_r`',
    '[^3]: `seq_inner_sym` (симметрия) и `seq_inner_sub_r` (линейность по разности во втором аргументе) в `ProcessL2BesselGeneral.v`; линейность по каждому аргументу в общем виде — `seq_inner_lin_r`, `seq_inner_lin_l`, сводно — `seq_inner_bilinear_symmetric` в `ProcessOrthonormalFourier.v` (индукция по $N$ и `ring`). Все — 0 аксиом.'));
  // 7. сноска 4: гипотеза Hon
  e1.push(whole('[^4]: `Hypothesis Hon : forall i j, seq_inner (e i) (e j) N',
    L('[^4]: `Hypothesis Hon : forall i j, (i < K0)%nat -> (j < K0)%nat -> seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)` в `ProcessL2Orthonormal.v` и `ProcessOrthonormalFourier.v`. Условию удовлетворяют стандартный базис (`std_basis_on`) и повёрнутый рациональный базис $(3/5,4/5)$, $(-4/5,3/5)$ (`rot_orthonormal`); $K_0§le N$ — `on_count_le_dim`. В `ProcessL2BesselGeneral.v`, `ProcessL2Parseval.v` и `ProcessBestApproximation.v` то же условие записано для всех номеров $i,j$; на $N$ координатах оно невыполнимо (`on_all_indices_unsat`), и теоремы под ним примеров не имеют. О системе Уолша–Адамара — ') + String.fromCharCode(167) + ' «Конкретная ортогональная система: Уолш–Адамар».'));
  // (знак параграфа вынесен из L(): при первом прогоне он был заменён обратной косой чертой; исправлено правкой шага 01а)
  // 8. сноска 6: ортогональность остатка
  e1.push(whole('[^6]: `proj_ortho`: ',
    L('[^6]: `proj_ortho_b` (`ProcessL2Orthonormal.v`): $§inner{e_K}{§sum_{k<K} c_k e_k}_N = 0$ при $K<K_0$. Отсюда `coef_e_resid_b`: $§inner{e_K}{f-P_K}_N = §inner{e_K}{f}_N$ — проекция не трогает ещё не снятую координату. Ортогональность остатка снятым направлениям, $§inner{e_j}{r_K}_N=0$ при $j<K§le K_0$, — `resid_ortho_b` (через `proj_coord_b`: $§inner{e_j}{§sum_{k<K} c_k e_k}_N=c_j$). Последние три — в `ProcessOrthonormalFourier.v`; все — 0 аксиом.')));
  // 9. сноска 7: тождество Пифагора
  e1.push(whole('[^7]: `resid_norm` в `ProcessL2BesselGeneral.v`',
    L('[^7]: `resid_norm_b` в `ProcessL2Orthonormal.v` ($K§le K_0$): частный случай общего тождества остатка для произвольных весов `gen_resid`, которое доказывается индукцией по $K$ через тождество $§norm{F-cE}^2 = §norm{F}^2 - 2c§inner{E}{F} + c^2§norm{E}^2$ (`seq_inner_resid`) и ортогональность проекции `proj_ortho_b`. 0 аксиом.')));
  // 10. сноска 8: наилучшее приближение
  e1.push(whole('[^8]: Тождество наилучшего приближения — `best_approx_eq`;',
    L('[^8]: Тождество наилучшего приближения — `best_approx_eq_b`; единственность (равенство $§Leftrightarrow$ $a_k=c_k$ при $k<K$) — `best_approx_unique_b` (через лемму «конечная сумма квадратов над ℚ равна нулю лишь когда каждое слагаемое нуль», `q_sum_sq_zero`); обе — в `ProcessOrthonormalFourier.v`. Следствие-минимум $§norm{f-P_K}^2§le§norm{f-§sum a_k e_k}^2$ — `best_approx_b` в `ProcessL2Orthonormal.v`. Все — при $K§le K_0$, 0 аксиом. Единственность здесь — *конечная*, на фиксированном диапазоне $k<K$; сходимость бесконечного ряда — предмет Главы 7.4.')));
  // 11. сноска 9: Бессель
  e1.push(whole('[^9]: `bessel_general` в `ProcessL2BesselGeneral.v`',
    L('[^9]: `bessel_b` в `ProcessL2Orthonormal.v` ($K§le K_0$): из `resid_norm_b` и неотрицательности нормы остатка одним шагом `lra`. 0 аксиом. Это общее неравенство Бесселя для произвольной конечной ортонормированной системы — не привязанное к конкретному базису.')));
  // 12. сноска 10: расщепление энергии
  e1.push(whole('[^10]: `energy_split` в `ProcessL2Parseval.v`',
    L('[^10]: `energy_split_b` в `ProcessL2Orthonormal.v` ($K§le K_0$): прямое следствие `resid_norm_b` (переписывание и `ring`). 0 аксиом.')));
  // 13. сноска 11: критерий полноты
  e1.push(whole('[^11]: `parseval_iff_complete` в `ProcessL2Parseval.v`',
    L('[^11]: `parseval_iff_complete_b` в `ProcessL2Orthonormal.v` ($K§le K_0$); опирается на `q_sum_sq_zero` («сумма квадратов нуль $§Rightarrow$ каждый член нуль» над ℚ) и тождество остатка `resid_norm_b`; промежуточная эквивалентность «Парсеваль $§Leftrightarrow$ нулевая норма остатка» — `parseval_iff_resid_zero_b`. 0 аксиом.')));
  // 14. место 1.2: сноска 12 — свидетель (3, 4) как пример критерия
  e1.push(whole('[^12]: `parseval_std_concrete` в `ProcessL2Parseval.v`',
    "[^12]: `parseval_3_4_from_criterion` в `ProcessOrthonormalFourier.v`: стандартный базис удовлетворяет `Hon` (`std_basis_on`), равенство Парсеваля для него выполнено при всяком $N$ и всякой $f$ (`parseval_std_all`), и по критерию `parseval_iff_complete_b` разложение восстанавливает обе координаты $f=(3,4)$. Само равенство $25=25$ — `parseval_std_concrete` в `ProcessL2Parseval.v`: проверяется `vm_compute`'ом — точной рациональной арифметикой. (Это пифагорова тройка $3,4,5$, прочитанная как сохранение энергии; сама тройка — рациональная точка единичной окружности, значение $t=1/2$ стереографической параметризации, выводимая, а не постулируемая — `PythagoreanTriples.v`.)"));
  // 15. сноска 13: имена критерия и полноты
  e1.push(inline('[^13]: Шапка `ProcessL2Parseval.v` помечает это прямо:',
    'доказан конечный критерий полноты.',
    'доказан конечный критерий полноты. Критерий — `parseval_iff_complete_b`; полнота системы из $N$ ортонормированных векторов — `full_on_recovers` и `full_on_parseval` (`ProcessOrthonormalFourier.v`), 0 аксиом.'));
}

// ---------- Глава VII.4 ----------
const e4 = [];
{
  const { old, inline, whole } = loader(REL4);
  // 1. разметка: закрывающая кавычка попала внутрь тега
  e4.push(inline('сходится к ней в L<sup>2</sup»>', 'L<sup>2</sup»>', 'L<sup>2</sup>»'));
  // 2. место 4.1: точное восстановление при K = N для всякого набора из N ортонормированных векторов
  e4.push({ old: old('усечении $N$, ошибка зануляется при достаточно большом $K$; для стандартного полного',
                     '$N$-направленного набора — точно при $K=N$: процесс усечения завершается *точным*'),
    neu: ['усечении $N$, ошибка зануляется при достаточно большом $K$; для всякого набора из $N$',
          'ортонормированных векторов (в частности, стандартного) — точно при $K=N$: процесс усечения завершается *точным*'] });
  // 3. сноска 1: опорный файл
  e4.push(whole('[^1]: Опорные файлы — `ProcessFourierSeriesL2.v`',
    L('[^1]: Опорный файл — `ProcessOrthonormalFourier.v` (каталог `src/process/`, 30 утверждений, 0 `Admitted`, 0 аксиом), поверх `ProcessL2Orthonormal.v` (Часть VI): условие ортонормированности наложено на первые $K_0$ векторов, теоремы доказаны для $K§le K_0$, и $K_0§le N$ (`on_count_le_dim`). В прежних `ProcessFourierSeriesL2.v` и `ProcessBestApproximation.v` те же утверждения записаны под условием ортонормированности при всех номерах, на $N$ координатах невыполнимым (`on_all_indices_unsat`). Процессное чтение предела — `ProcessL2RieszFischer.v`. Имена — в сносках ниже.')));
  // 4. сноска 3: тождество ошибки
  e4.push(whole('[^3]: `fourier_error_eq` в `ProcessFourierSeriesL2.v`',
    L('[^3]: `fourier_error_eq_b` в `ProcessOrthonormalFourier.v`: $§norm{f-P_K}^2=§norm{f}^2-§texttt{captured}(c,K)$ при $K§le K_0$, где `captured`$(c,K)=§sum_{k<K}c_k^2$. Прямое следствие `resid_norm_b` (Часть VI). Если $K_0$ векторов полны для $f$, эта разность есть сумма квадратов отброшенных коэффициентов $§sum_{K§le k<K_0}c_k^2$ — `fourier_error_is_tail_b`. 0 аксиом.')));
  // 5. место 4.3: сноска 4 — неотрицательность и Бессель
  e4.push(whole('[^4]: `fourier_error_nonneg`;',
    '[^4]: `ferr_nonneg` — неотрицательность ошибки; она верна для любого семейства $e$ (сумма квадратов). Неравенство Бесселя следует из неё вместе с тождеством ошибки — `bessel_from_error_b` (то же, что `bessel_b`, Глава 7.1). Обе — в `ProcessOrthonormalFourier.v`, 0 аксиом.'));
  // 6. сноска 5: монотонность
  e4.push(whole('[^5]: `fourier_error_monotone`;',
    L("[^5]: `fourier_error_monotone_b` ($K§le K'§le K_0$); опирается на монотонность захваченной энергии (`captured_mono`, Глава 7.5). Точнее: очередной коэффициент уменьшает ошибку ровно на свой квадрат, $§norm{f-P_{K+1}}^2=§norm{f-P_K}^2-c_K^2$, — `fourier_error_step_b`. Без ортонормированности ошибка может расти — `monotone_fails_without_on`. Все — в `ProcessOrthonormalFourier.v`, 0 аксиом.")));
  // 7. сноска 6: наилучшее приближение
  e4.push(whole('[^6]: `fourier_partial_best` в `ProcessFourierSeriesL2.v`',
    L('[^6]: `fourier_partial_best_b` в `ProcessOrthonormalFourier.v` (она же `best_approx_b` из `ProcessL2Orthonormal.v`): $§norm{f-P_K}^2§le§norm{f-§sum_{k<K}a_k e_k}^2$ для любых весов $a_k$, $K§le K_0$; единственность минимума — `best_approx_unique_b`. 0 аксиом.')));
  // 8. место 4.3: сноска 7 — критерий нуля
  e4.push(whole('[^7]: `fourier_error_zero_iff`:',
    L('[^7]: `fourier_error_zero_iff_b`: $§norm{f-P_K}^2=0 §Leftrightarrow §sum_{k<K}c_k^2=§norm{f}^2$ — из тождества ошибки; «нулевая ошибка $§Leftrightarrow$ $P_K(m)=f(m)$ при всех $m<N$» — `fourier_error_zero_iff_recovers_b`, через критерий полноты `parseval_iff_complete_b` (Глава 7.1). Точное восстановление при $K=N$ для $N$ ортонормированных векторов — `fourier_truncation_ends_exactly` (через `full_on_recovers`); для стандартного базиса — `std_truncation_ends_exactly`, для повёрнутого — `rot_truncation_ends_exactly`. Все — в `ProcessOrthonormalFourier.v`, 0 аксиом.')));
  // 9. сноска 8: шапка нового файла
  e4.push(inline('[^8]: Шапки: `ProcessFourierSeriesL2.v`',
    '`ProcessBestApproximation.v` — Rules: $P_K$ — единственный минимум невязки.',
    L('`ProcessBestApproximation.v` — Rules: $P_K$ — единственный минимум невязки. `ProcessOrthonormalFourier.v` — Roles: `ferr` — квадрат ошибки как функция стадии $K$; P4: $K§le K_0§le N$, процесс усечений заканчивается точным восстановлением при $K=N$.')));
}

const out = []; let n = 0;
for (const [rel, es] of [[REL1, e1], [REL4, e4]]) {
  out.push('@@FILE ' + rel);
  for (const e of es) { out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END'); n++; }
}
fs.writeFileSync(path.join(__dirname, 'шаг-01-главы-VII1-и-VII4.txt'), out.join('\n') + '\n');
console.log('шаг-01-главы-VII1-и-VII4.txt: правок ' + n + ' (VII.1 — ' + e1.length + ', VII.4 — ' + e4.length + ')');
