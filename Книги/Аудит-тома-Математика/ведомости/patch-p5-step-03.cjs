// Часть V, шаг 3 (2026-11-12, слово автора «Да — вносим»): точные формы следствий основной теоремы (глава V.6).
// Запуск: node patch-p5-step-03.cjs   (затем tom-links.cjs relocate + merge)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 3, слово автора)';
const F = 'src/analysis/FTC.v', PF = 'src/process/ProcessFTC.v';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part05-ch06.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0;
function set(prefix, fields) {
  const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  Object.assign(hit[0], fields); n++;
}
set('То есть $\\int_a^b c = c (b-a) = f(b)-f(a)$ *точно*', {
  theorem: 'ftc_error_const_exact', file: PF,
  claim: 'То есть $\\int_a^b c = c (b-a) = f(b)-f(a)$ *точно*: ошибка тождественно нулевая на каждом уровне (лемма `ftc_error_const_exact`).',
  verdict: 'ok',
  note: DONE + ' — слова те же, добавлено имя: шагом 3 доказаны integral_process_const_exact (integral_process (fun _ => c) a b n == c * (b - a) при всяком n) и ftc_error_const_exact (ftc_error_process (fun x => c * x) (fun _ => c) a b n == 0); прежняя ftc_error_const давала это только как process_equiv; Closed under the global context' });
set('леммы вроде `udiff_implies_bounded`', {
  theorem: 'udiff_bounded_on', file: F,
  claim: 'леммы вроде `udiff_bounded_on` (оценка значений функции на всём отрезке через границу производной) и `lipschitz_bounded` (ограниченность липшицевой функции) помогают контролировать классы функций',
  verdict: 'ok',
  note: DONE + ': было «udiff_implies_bounded (оценка значений функции через производную)» — та лемма оценивает одно значение в последнем узле одной сетки; шагом 3 добавлена udiff_bounded_on: Proper f -> udiff_on f f\' a b -> (|f\'| <= M на отрезке) -> 0 <= M -> forall x из отрезка, |f x| <= |f a| + M (b - a); Closed under the global context' });
set('Лемма `ftc_nonneg_integral`', {
  theorem: 'nonneg_deriv_nondecreasing', file: F,
  claim: 'Содержательно: неотрицательная производная даёт неубывающее приращение — $f(a)\\le f(b)$ (теорема `nonneg_deriv_nondecreasing`, для функции, уважающей равенство рациональных).',
  verdict: 'ok',
  note: DONE + ': было «Лемма ftc_nonneg_integral: … неотрицательна с точностью до сеточной ошибки. Содержательно: неотрицательная производная даёт неубывающее приращение»; шагом 3 добавлены riemann_sum_deriv_nonneg_exact (точная неотрицательность суммы на каждом уровне) и nonneg_deriv_nondecreasing : Proper f -> udiff_on f f\' a b -> (f\' >= 0 на отрезке) -> f a <= f b; Closed under the global context' });
set('Лемма `ftc_monotone`', {
  theorem: 'nonneg_deriv_nondecreasing', file: F,
  claim: 'Теорема `nonneg_deriv_nondecreasing`: при $f\'\\ge 0$ приращение неотрицательно, $f(a)\\le f(b)$; её сеточная предшественница — лемма `ftc_monotone`, с зазором на одном уровне сетки.',
  verdict: 'ok',
  note: DONE + ': было «Лемма ftc_monotone: при f\' >= 0 функция растёт на сетке (приращение неотрицательно)» — у ftc_monotone зазор eps, один уровень, последний узел; точная форма — nonneg_deriv_nondecreasing' });
set('`ftc_strict_monotone` (то же, что', {
  claim: '`ftc_strict_monotone` (то же, что `pos_deriv_increases` из § 5.4) даёт положительное приращение до последнего узла сетки при производной, отделённой от нуля.',
  note: DONE + ': было «даёт строгий рост» — лемма даёт положительность приращения до последнего узла на одном уровне сетки; слова приведены к утверждению' });
set('Отдельной теоремы вида', {
  theorem: 'udiff_bounded_deriv_lipschitz', file: F,
  claim: 'Мост от дифференцируемости к липшицевости тоже есть: теорема `udiff_bounded_deriv_lipschitz` (`FTC.v`) — равномерно дифференцируемая функция с ограниченной производной ($|f\'|\\le M$ на отрезке) липшицева на этом отрезке с константой $M$; условие — функция уважает равенство рациональных.',
  verdict: 'ok',
  note: DONE + ': было «Отдельной теоремы вида udiff_on => Lipschitz_on в стандартной форме файл не содержит» (статус был честен); шагом 3 теорема добавлена: Proper f -> udiff_on f f\' a b -> (|f\'| <= M на отрезке) -> 0 <= M -> Lipschitz_on f a b M (определение FTC.v:43, константа 0 <= K); Closed under the global context' });
set('Что есть точно: `lipschitz_bounded`', {
  theorem: 'udiff_bounded_on', file: F,
  claim: 'Из неё следует `udiff_bounded_on` — ограниченность значений на всём отрезке. Рядом стоят `lipschitz_bounded` — ограниченность функции, если она уже липшицева, — и сеточные MVT-оценки приращений (например, `bounded_deriv_bounded_increment` из § 5.4).',
  verdict: 'ok',
  note: DONE + ': было «udiff_implies_bounded — оценка значений через слой теоремы о среднем»; названа новая udiff_bounded_on (выведена из udiff_bounded_deriv_lipschitz и lipschitz_bounded)' });
set('12 Qed, 0 axioms', {
  claim: '14 Qed, 0 axioms',
  note: DONE + ': после шага 3 в ProcessFTC.v 14 Qed (шапка файла исправлена); до шага 2 на странице стояло 8 при девяти' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part05-ch06.json: записей изменено ' + n + ', всего ' + j.records.length);
