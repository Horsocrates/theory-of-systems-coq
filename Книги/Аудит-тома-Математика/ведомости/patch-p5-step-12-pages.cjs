// Часть V, шаг 12, страницы (2026-11-12, слово автора «Да — вносим десять мест»): глава V.5.
// Запуск: node patch-p5-step-12-pages.cjs   (затем tom-links.cjs relocate + merge по ведомости главы V.5)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 12, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part05-ch05.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
function set(prefix, fields) {
  const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  Object.assign(hit[0], fields); n++;
}
function add(rec) {
  if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
  j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
}
const RI = 'src/RiemannIntegration.v', PA = 'src/process/ProcessAnalysis.v', PI = 'src/process/ProcessIntegral.v', IA = 'src/IntegralApplications.v';
set('В репозитории есть *три разных* определения с именем `riemann_sum`', {
  claim: 'В репозитории есть *три разных* определения с именем `riemann_sum`: это, основное, из `RiemannIntegration.v` (левая сумма по `walk_point`); демонстрационное в `ProcessAnalysis.v`; и ещё одно в `ProcessMCT.v` (сумма по произвольной последовательности узлов с общим весом).',
  verdict: 'ok',
  note: DONE + ': было — третьим названо riemann_sum_01 (другое имя, stdlib/ProcessIntegration.v), а process/ProcessMCT.v не назван. Объявлений riemann_sum три: RiemannIntegration.v:39, process/ProcessAnalysis.v:110, process/ProcessMCT.v:111.' });
set('интеграл константы $c$ на отрезке есть $c$ (`integral_constant`)', {
  claim: 'интеграл константы $c$ на отрезке $[0,1]$ есть $c$ (`integral_constant`)', verdict: 'ok',
  note: DONE + ': integral_constant : step_integral (mkStep c 0 1 le_0_1) == c — ступень на [0,1]; на общем отрезке значение c * (b - a). Отрезок назван.' });
set('Лемма `riemann_sum_abs_bound`: если $|f|\\le M$ в узлах, то', {
  claim: '`riemann_sum_abs_bound`: если $|f|\\le M$ в узлах и шаг неотрицателен, то $|\\texttt{riemann\\_sum} f a \\texttt{step} n|\\le M\\cdot n\\cdot\\texttt{step}$.',
  verdict: 'ok',
  note: DONE + ': в лемме стоят условия 0 <= step и 0 <= M; без условия на шаг оценка неверна (контрпример помощника: step = -1). Условие названо.' });
set('Лемма `riemann_sum_global_bound`: при', {
  claim: 'Лемма `riemann_sum_global_bound`: при $\\mathrm{lo}\\le f\\le \\mathrm{hi}$ в узлах и неотрицательном шаге сумма из $n$ слагаемых зажата между $\\mathrm{lo}\\cdot n\\cdot\\texttt{step}$ и $\\mathrm{hi}\\cdot n\\cdot\\texttt{step}$.',
  verdict: 'ok', note: DONE + ': в лемме стоит условие 0 <= step; оно названо.' });
set('Подставив, получаем для конечной суммы процесса $\\texttt{RS}_n$:', {
  theorem: 'integral_process_abs_bound', file: PI,
  claim: 'Подставив, получаем для конечной суммы процесса $\\texttt{RS}_n$ (леммы `integral_process_abs_bound` и `integral_process_global_bound`):',
  note: DONE + ': формулы стояли выводом главы без леммы; добавлены integral_process_abs_bound : a < b -> 0 <= M -> (|f| <= M в узлах уровня n) -> |integral_process f a b n| <= M * (b - a) и integral_process_global_bound. Closed under the global context.' });
set('Сумма приращений по узлам равна полному приращению от $a$ до конца сетки — и это совпадение', {
  claim: 'Сумма приращений по узлам равна полному приращению от $a$ до конца сетки — без погрешности и без условий на $f$. *Лейбницево-точно* здесь совпадение узлов',
  verdict: 'ok',
  note: DONE + ': было «совпадение лейбницево-точное» о равенстве суммы и приращения — telescope_collapse даёт равенство рациональных ==; лейбницево равенство ложно (пример помощника: 16#16 против 4#4). Лейбницево-точно совпадение соседних узлов (walk_point a s (S k) = walk_point a s k + s по reflexivity). Довести формализацию нельзя.' });
set('Файл `IntegralApplications.v` содержит правило произведения для интеграла', {
  claim: 'Файл `IntegralApplications.v` содержит правило произведения для равномерной дифференцируемости (`udiff_product`: приращение произведения раскладывается на три слагаемых — тождество `product_decomp`, — и $\\varepsilon$ дробится на три части, как в правиле произведения производной § 5.4)',
  verdict: 'ok',
  note: DONE + ': было «правило произведения для интеграла» — udiff_product говорит о udiff_on произведения; интегральная форма — ftc_product. Доказательство udiff_product теперь вызывает лемму product_decomp (раньше тождество выводилось на месте, лемма нигде не применялась).' });
set('с тем же $\\varepsilon/3$-разложением `product_decomp`', {
  claim: 'приращение произведения раскладывается на три слагаемых — тождество `product_decomp`',
  verdict: 'ok',
  note: DONE + ': было «то же разложение, что у производной» — у deriv_product тождество другое; общее — дробление eps на три части. product_decomp теперь применяется в udiff_product.' });
set('единственность первообразной (`antiderivative_unique`: две функции с одной производной имеют', {
  theorem: 'antiderivative_unique_exact', file: IA,
  claim: 'единственность первообразной (`antiderivative_unique_exact`: две функции с одной производной имеют равные приращения на отрезке',
  verdict: 'ok',
  note: DONE + ': было — «равные приращения» приписаны antiderivative_unique, которая даёт близость приращений на уровне сетки. Добавлена antiderivative_unique_exact : udiff_on f h a b -> udiff_on g h a b -> f b - f a == g b - g a — без условия, что функции уважают Qeq (мост — continuous_at_qeq_values). Closed under the global context.' });
set('Интеграл $\\int_0^1 1$ равен $1$ на каждом уровне.', {
  theorem: 'integral_one_all_levels', file: PA,
  claim: 'Интеграл $\\int_0^1 1$ равен $1$ на каждом уровне (`integral_one_all_levels`).',
  verdict: 'ok',
  note: DONE + ': было доказано для трёх уровней (K = 0, 1, 2). Добавлена integral_one_all_levels : forall K, process_integral (fun _ => 1) K == 1. Closed under the global context.' });
set('Файл `ProcessAnalysis.v` содержит *свои* `process_derivative`', {
  claim: 'Файл `ProcessAnalysis.v` содержит *свои* определения: `process_derivative`, `riemann_sum` и `process_integral`. Имя `riemann_sum` совпадает с основным из `RiemannIntegration.v`, а определение другое',
  verdict: 'ok',
  note: DONE + ': было «имена совпадают» — совпадает одно из трёх (riemann_sum); основные определения производной и интеграла носят имена deriv_process и integral_process.' });
// две записи с одной цитатой о сокращённых именах
{
  const h = j.records.filter((r) => norm(r.claim).startsWith('оценки сумм (`abs_bound`, `global_bound`)'));
  if (h.length !== 2) throw new Error('ожидались две записи о сокращённых именах, найдено ' + h.length);
  Object.assign(h[0], { theorem: 'riemann_sum_abs_bound', file: RI, claim: 'оценки сумм (`riemann_sum_abs_bound`, `riemann_sum_global_bound`)', verdict: 'ok', note: DONE + ': было сокращённое имя abs_bound; полное — riemann_sum_abs_bound.' });
  Object.assign(h[1], { theorem: 'riemann_sum_global_bound', file: RI, claim: '`riemann_sum_global_bound`); телескоп (`telescope_collapse`)', verdict: 'ok', note: DONE + ': было сокращённое имя global_bound; полное — riemann_sum_global_bound.' });
  n += 2;
}
set('`StepIntegral.v` к тому же короток и заявляет', {
  claim: '`StepIntegral.v` к тому же короток и заявляет « 17 Qed, 0 Admitted, 0 axioms ».', verdict: 'ok',
  note: DONE + ': в файле 17 Qed; шапка файла (стояло 20) и число на странице приведены к этому.' });
add({ theorem: 'antiderivative_unique', file: IA,
  claim: 'её сеточная предшественница `antiderivative_unique` даёт близость приращений на уровне сетки',
  note: 'antiderivative_unique : для всякого eps найдётся уровень N, на котором приращения f и g до последнего узла сетки различаются не больше чем на eps * (b - a). Closed under the global context.' });
add({ theorem: 'ftc_product', file: IA,
  claim: 'его интегральную форму (`ftc_product`)',
  note: 'Лемма существует (IntegralApplications.v): интегральная форма правила произведения. Closed under the global context.' });
add({ theorem: 'integral_process_global_bound', file: PI,
  claim: '`integral_process_global_bound`):',
  note: 'Новая лемма шага 12: при lo <= f <= hi в узлах уровня n — lo * (b - a) <= integral_process f a b n <= hi * (b - a). Closed under the global context.' });
add({ theorem: 'process_derivative_agrees', file: PA,
  claim: 'Для производной две записи согласованы леммой: их значения совпадают на каждом уровне (`process_derivative_agrees`).',
  note: 'Новая лемма шага 12: process_derivative f x K == ProcessDerivative.deriv_process f x K. Closed under the global context.' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part05-ch05.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
