// Часть V, шаг 11, страницы (2026-11-12, слово автора «Да — вносим десять мест»): глава V.4.
// Запуск: node patch-p5-step-11-pages.cjs   (затем tom-links.cjs relocate + merge по ведомости главы V.4)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 11, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part05-ch04.json');
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
const MVT = 'src/MeanValueTheorem.v', DIF = 'src/Differentiation.v';
const LIP = ' Добавлена bounded_deriv_lipschitz : udiff_on f f\' a b -> (|f\'| <= M на отрезке) -> forall x y из отрезка, |f y - f x| <= M * |y - x|, и её запись в каноне § 5.3 — bounded_deriv_Lipschitz_on (при 0 < M); без условия, что функция уважает равенство рациональных (мост — continuous_at_qeq_values). Closed under the global context.';
set('Тот же приём применялся к `continuous_at` в § 5.3', {
  file: DIF,
  claim: 'Тот же приём применён к местному определению `continuous_at` в `Differentiation.v` (§ 4.3.1); это сознательная деталь, не недосмотр.',
  verdict: 'ok',
  note: DONE + ': было «применялся к continuous_at в § 5.3» — приём ненулевого шага стоит в местном определении Differentiation.v, а определение § 5.3 (Topology.v) говорит обо всех точках окрестности.' });
set('Про статус аксиом: `ProcessDerivative.v` в шапке заявляет', {
  claim: 'Про статус аксиом: `ProcessDerivative.v` в шапке заявляет « 0 axioms, 17 Qed »; он импортирует `ProcessCore`, `ProcessArithmetic` и `Differentiation`.',
  verdict: 'ok', note: DONE + ': в файле 17 Qed; шапка файла (стояло 16) и число на странице приведены к этому.' });
set('| равномерная дифференцируемость (`udiff`)', {
  theorem: 'udiff_on', file: MVT,
  claim: '| равномерная дифференцируемость (`udiff_on`) | усиление для среднего | Rule |', verdict: 'ok',
  note: DONE + ': было сокращённое имя udiff; полное — udiff_on.' });
set('А липшицевость § 4.7.3 показывает, как Rules производной', {
  theorem: 'bounded_deriv_Lipschitz_on', file: MVT, verdict: 'ok',
  note: DONE + ' — слова те же, доведена формализация: раньше из производной выводилась только оценка возле одной точки (bounded_deriv_lipschitz_local).' + LIP });
set('если функция дифференцируема в точке, то она в этой точке непрерывна. В `Differentiation.v`', {
  claim: 'если функция дифференцируема в точке, то она в этой точке непрерывна. В `Differentiation.v` это `deriv_implies_continuous`: из `has_derivative f x L` следует `continuous_at f x`, где `continuous_at` — определение непрерывности через приращение, записанное в самом `Differentiation.v`',
  verdict: 'ok',
  note: DONE + ': было «определение непрерывности из § 5.3» — это одноимённое местное, более слабое определение (проколотая окрестность). Мост записан: topo_continuous_implies_punctured; обратно — deriv_implies_topo_continuous при условии, что функция уважает Qeq; без условия неверно (derivative_does_not_give_topo_continuity). Заодно имя has_derivative f x L, разорванное переносом строки, собрано.' });
set('В `Differentiation.v` это `deriv_product` — самое длинное доказательство файла', {
  claim: 'В `Differentiation.v` это `deriv_product` — самое длинное доказательство файла (`SECTION 4`, около двухсот строк).',
  verdict: 'ok', note: DONE + ': было «около ста пятидесяти строк»; в доказательстве 201 строка.' });
set('Теорема *не* утверждает полной формы « $f$ постоянна на всём отрезке ».', {
  theorem: 'zero_deriv_constant', file: MVT,
  claim: 'Полная форма — « $f$ постоянна на всём отрезке » — доказана отдельной теоремой `zero_deriv_constant`: если производная равна нулю на отрезке, то $f(x)=f(y)$ для любых $x,y$ из него.',
  note: DONE + ': было — глава честно писала, что полная форма не доказывается. Добавлена zero_deriv_constant : udiff_on f f\' a b -> (f\' x == 0 на отрезке) -> forall x y из отрезка, f x == f y. Closed under the global context.' });
set('Третье следствие — липшицевость. Лемма `bounded_deriv_lipschitz_local` даёт локальную оценку', {
  verdict: 'ok',
  note: DONE + ': локальная лемма описана верно; рядом теперь названа теорема для всего отрезка.' + LIP });
set('В § 5.3 липшицевость вводилась *как условие*', {
  theorem: 'bounded_deriv_Lipschitz_on', file: MVT, verdict: 'ok',
  note: DONE + ' — слова те же («теперь липшицевость выводится — из ограниченной производной»), доведена формализация.' + LIP });
set('`bounded_deriv_bounded_increment` — сеточное следствие теоремы о среднем', {
  claim: '`bounded_deriv_bounded_increment` — сеточное следствие теоремы о среднем — и монотонность с липшицевостью как дальнейшие следствия; точные формы на всём отрезке — `zero_deriv_constant`, `pos_deriv_strictly_increasing`, `bounded_deriv_lipschitz`.',
  verdict: 'ok', note: DONE + ': к итогу добавлены три точные теоремы шага 11.' });
set('Все три опорных файла — `Differentiation.v`, `ProcessDerivative.v`, `MeanValueTheorem.v`', {
  claim: 'Все три опорных файла — `Differentiation.v`, `ProcessDerivative.v`, `MeanValueTheorem.v` — в своих шапках заявляют статус « AXIOMS: none » (`ProcessDerivative.v` — « 0 axioms, 17 Qed »).',
  verdict: 'ok', note: DONE + ': число приведено к файлу (17 Qed).' });
set('сеточная теорема о среднем и её следствия — монотонность и липшицевость.*', {
  theorem: 'bounded_deriv_lipschitz', file: MVT, verdict: 'ok',
  note: DONE + ' — слова те же, доведена формализация.' + LIP });
add({ theorem: 'continuous_at_qeq_values', file: MVT,
  claim: 'функция, непрерывная в двух равных как числа точках, принимает в них равные значения (`continuous_at_qeq_values`)',
  note: 'Новая лемма шага 11: x == x\' -> continuous_at f x -> continuous_at f x\' -> f x == f x\' (непрерывность — в смысле Differentiation.v). Closed under the global context.' });
add({ theorem: 'pos_deriv_strictly_increasing', file: MVT,
  claim: 'Точную форму даёт теорема `pos_deriv_strictly_increasing`: если производная отделена снизу положительным числом, то $f(x)<f(y)$ для любых $x<y$ из отрезка.',
  note: 'Новая теорема шага 11: udiff_on f f\' a b -> (c <= f\' x на отрезке) -> 0 < c -> forall x < y из отрезка, f x < f y. Closed under the global context.' });
add({ theorem: 'bounded_deriv_lipschitz', file: MVT,
  claim: 'На всём отрезке липшицевость даёт теорема `bounded_deriv_lipschitz`: при равномерной дифференцируемости и $|f\'|\\le M$ на $[a,b]$ имеем $|f(y)-f(x)|\\le M\\,|y-x|$ для любых двух точек отрезка',
  note: 'Новая теорема шага 11. Closed under the global context.' });
add({ theorem: 'bounded_deriv_Lipschitz_on', file: MVT,
  claim: 'в терминах § 5.3 это `bounded_deriv_Lipschitz_on`.',
  note: 'Новое следствие шага 11: 0 < M -> udiff_on f f\' a b -> (|f\'| <= M на отрезке) -> Continuity.Lipschitz_on f a b M. Closed under the global context.' });
add({ theorem: 'topo_continuous_implies_punctured', file: DIF,
  claim: 'из него местное следует (`topo_continuous_implies_punctured`)',
  note: 'Новая лемма шага 11: Topology.continuous_at f x -> continuous_at f x. Closed under the global context.' });
add({ theorem: 'deriv_implies_topo_continuous', file: DIF,
  claim: 'а обратно — только для функции, уважающей равенство рациональных (`deriv_implies_topo_continuous`)',
  note: 'Новая теорема шага 11: (forall u v, u == v -> f u == f v) -> has_derivative f x L -> Topology.continuous_at f x. Closed under the global context.' });
add({ theorem: 'derivative_does_not_give_topo_continuity', file: DIF,
  claim: 'без этого условия переход неверен, и контрпример проверен (`derivative_does_not_give_topo_continuity`).',
  note: 'Новая теорема шага 11: exists f x L, has_derivative f x L /\\ ~ Topology.continuous_at f x; свидетель — rep_fn (различает записи одного числа), точка 2#2, производная 0. Closed under the global context.' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part05-ch04.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
