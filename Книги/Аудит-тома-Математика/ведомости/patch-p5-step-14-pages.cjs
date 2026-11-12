// Часть V, шаг 14, страницы (2026-11-12, слово автора «Да — вносим шесть мест»): условие Proper снято.
// Запуск: node patch-p5-step-14-pages.cjs   (затем tom-links.cjs relocate + merge по ведомостям глав V.5 и V.6)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 14, слово автора)';
const NOTE = ' После шага 14 Части V посылки Proper (Qeq ==> Qeq) f у теоремы нет: на отрезке это свойство следует из равномерной дифференцируемости (MeanValueTheorem.udiff_respects_qeq, udiff_walk_endpoint_value). Closed under the global context.';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  return {
    set(prefix, fields, append) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
      if (append) hit[0].note = (hit[0].note || '').replace(/\s*$/, '') + append;
      Object.assign(hit[0], fields); n++;
    },
    add(rec) {
      if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); },
  };
}
const MVT = 'src/MeanValueTheorem.v';
const a = open('part05-ch05.json');
a.set('равномерная дифференцируемость `udiff_on` из § 5.4 окажется именно тем условием', {}, NOTE);
a.set('Для констант это видно сразу (§ 5.2.1); для производных равномерно дифференцируемых функций', {}, NOTE);
a.set('Для двух классов это доказано. Для констант — леммой `integral_process_const`.', {
  claim: 'Для двух классов это доказано. Для констант — леммой `integral_process_const`. Для производной равномерно дифференцируемой функции — теоремой `ftc_process_converges`: процесс её Римановых сумм эквивалентен постоянному процессу приращения $f(b)-f(a)$ и потому есть процесс Коши (`ftc_integral_process_Cauchy`).',
  note: DONE + ': было «условие — функция уважает равенство рациональных (§ 5.5.2)» — оговорка снята вместе с посылкой. ftc_process_converges : udiff_on f f\' a b -> process_equiv (integral_process f\' a b) (const_process (f b - f a)). Closed under the global context.' });
a.save();
const b = open('part05-ch06.json');
b.set('Лемма `walk_endpoint_qeq` даёт, что $y_{N+1}$ равна $b$ в смысле отношения `Qeq`; но чтобы', {
  claim: 'Лемма `walk_endpoint_qeq` даёт, что $y_{N+1}$ равна $b$ в смысле отношения `Qeq`; но чтобы перенести это под $f$ и прочесть $f(y_{N+1})$ как $f(b)$, нужно, чтобы $f$ принимала в этих двух записях одного числа равные значения.',
  note: DONE + ': было «функция f должна уважать Qeq (быть Proper) … требует отдельной оговорки» — для равномерно дифференцируемой функции оговорка не нужна: udiff_walk_endpoint_value. walk_endpoint_qeq — Closed under the global context.' });
b.set('Теорема `ftc_is_process_construction` предъявляет этот процесс ошибки', {}, NOTE);
b.set('Определения `ProcessFTC.v` записывают ошибку основной теоремы в процессной форме', {}, NOTE);
b.set('Лемма `walk_endpoint_qeq` даёт $y_{N+1}=b$ в смысле `Qeq`; чтение', {
  claim: 'Лемма `walk_endpoint_qeq` даёт $y_{N+1}=b$ в смысле `Qeq`, а равномерная дифференцируемость — что значения $f$ в этих двух точках равны (`udiff_walk_endpoint_value`).',
  note: DONE + ': было «чтение f(y_{N+1}) как f(b) корректно, когда f уважает Qeq» — условие заменено доказанным фактом.' });
b.set('леммы вроде `udiff_bounded_on` (оценка значений функции на всём отрезке', {}, NOTE);
b.set('Содержательно: неотрицательная производная даёт неубывающее приращение', {
  claim: 'Содержательно: неотрицательная производная даёт неубывающее приращение — $f(a)\\le f(b)$ (теорема `nonneg_deriv_nondecreasing`).',
  note: DONE + ': было «для функции, уважающей равенство рациональных» — оговорка снята вместе с посылкой. nonneg_deriv_nondecreasing : udiff_on f f\' a b -> (f\' >= 0 на отрезке) -> f a <= f b. Closed under the global context.' });
b.set('Мост от дифференцируемости к липшицевости тоже есть: теорема `udiff_bounded_deriv_lipschitz`', {
  claim: 'Мост от дифференцируемости к липшицевости тоже есть: теорема `udiff_bounded_deriv_lipschitz` (`FTC.v`) — равномерно дифференцируемая функция с ограниченной производной ($|f\'|\\le M$ на отрезке) липшицева на этом отрезке с константой $M$.',
  note: DONE + ': было «условие — функция уважает равенство рациональных» — оговорка снята вместе с посылкой. udiff_bounded_deriv_lipschitz : udiff_on f f\' a b -> (|f\'| <= M на отрезке) -> 0 <= M -> Lipschitz_on f a b M. Closed under the global context.' });
b.add({ theorem: 'udiff_walk_endpoint_value', file: MVT,
  claim: 'функция, непрерывная в двух равных как числа точках, принимает в них равные значения (`udiff_walk_endpoint_value`).',
  note: 'Новая лемма шага 14: udiff_on f f\' a b -> f (walk_point a ((b - a) / (N+1)) (N+1)) == f b — значение в последнем узле сетки равно значению в b; из continuous_at_qeq_values и udiff_continuous_at. Closed under the global context.' });
b.save();
