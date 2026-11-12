// Часть V, шаг 13, страницы (2026-11-12, слово автора «Да» — вносим четыре места): глава V.6.
// Запуск: node patch-p5-step-13-pages.cjs   (затем tom-links.cjs relocate + merge по ведомости главы V.6)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 13, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part05-ch06.json');
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
const F = 'src/analysis/FTC.v', IA = 'src/IntegralApplications.v';
set('Совпадение *лейбницево-точное*, поскольку узлы заданы рекурсивной', {
  claim: 'Равенство здесь — равенство рациональных чисел (`Qeq`). Лейбницево-точны сами узлы: `walk_point` из § 5.4 задана рекурсивно',
  verdict: 'ok',
  note: DONE + ': было «совпадение лейбницево-точное» — telescope_collapse даёт ==; лейбницево равенство ложно (контрпример помощника: 864#1296 против 24#36). Лейбницево-точны узлы. Довести формализацию нельзя; слова шапки RiemannIntegration.v приведены к тому же.' });
set('Она понадобится в § 6.5: в правиле произведения', {
  claim: 'В § 6.5 похожий контроль понадобится для множителей — там он входит прямо в условия: правило произведения и интегрирование по частям требуют границ $M_f, M_g, M_{f\'}, M_{g\'}$ на значения функций и производных.',
  verdict: 'ok',
  note: DONE + ': было «она понадобится в § 6.5 … эта лемма даёт нужный контроль» — ftc_absolute_value_bound нигде не используется; в udiff_product, ftc_product, integration_by_parts границы — посылки о значениях функций и производных.' });
set('Доказательство — `ftc_product` плюс линейность Римановых сумм', {
  theorem: 'integration_by_parts', file: IA,
  claim: 'Доказательство — `ftc_product` плюс аддитивность Римановых сумм (`riemann_sum_add`).',
  verdict: 'ok',
  note: DONE + ': было «(riemann_sum_add, riemann_sum_sub)» — в доказательстве integration_by_parts леммы riemann_sum_sub нет: она объявлена в analysis/FTC.v, который сам подключает IntegralApplications.v.' });
set('линейность Римановых сумм (`riemann_sum_add`, `riemann_sum_sub`)', {
  claim: 'аддитивность Римановых сумм (`riemann_sum_add`).',
  note: 'riemann_sum_add применяется в доказательстве integration_by_parts; слова приведены к этому шагом 13 Части V.' });
set('Есть только *аффинный* случай: `udiff_chain_affine` (`FTC.v`)', {
  claim: 'Есть только *аффинный* случай: `udiff_chain_affine` (`FTC.v`) — цепное правило для внутренней функции $g = c\\cdot x + d$ при $c>0$, и `udiff_chain_affine_neg` при $c<0$; обе — для внешней функции, уважающей равенство рациональных.',
  note: DONE + ' — добавлено неназванное условие: у обеих цепных лемм посылка Proper (Qeq ==> Qeq) f.' });
set('`udiff_chain_affine_neg` при $c<0$.', {
  claim: '`udiff_chain_affine_neg` при $c<0$; обе — для внешней функции, уважающей равенство рациональных.',
  note: 'Лемма существует (analysis/FTC.v); после шага 13 Части V она применяется в ftc_u_substitution_affine_neg.' });
set('На них построена аффинная замена переменной в интеграле `ftc_u_substitution_affine`.', {
  claim: 'На них построены леммы `ftc_u_substitution_affine` ($c>0$) и `ftc_u_substitution_affine_neg` ($c<0$): Риманова сумма функции $f\'(cx+d)\\cdot c$ по отрезку $[a,b]$ приближает приращение $f(cx+d)$ — сеточная основная теорема для сложной функции.',
  verdict: 'ok',
  note: DONE + ': было — «на них построена аффинная замена» при одной применённой лемме (c > 0). Добавлена ftc_u_substitution_affine_neg (c < 0) и сама замена на уровне сумм — riemann_sum_affine_subst. Closed under the global context.' });
add({ theorem: 'ftc_u_substitution_affine_neg', file: F,
  claim: '`ftc_u_substitution_affine_neg` ($c<0$)',
  note: 'Новая лемма шага 13: при c < 0 и udiff_on f f\' (c*b+d) (c*a+d) Риманова сумма f\'(cx+d)*c по [a,b] приближает приращение f(cx+d) с точностью eps*(b-a) на некотором уровне. Closed under the global context.' });
add({ theorem: 'riemann_sum_affine_subst', file: F,
  claim: 'Саму замену на уровне сумм даёт лемма `riemann_sum_affine_subst`: сумма функции $\\varphi(cx+d)\\cdot c$ по сетке с шагом $s$ равна сумме функции $\\varphi$ по сетке с шагом $c\\cdot s$ от точки $ca+d$ — точно, при любом знаке $c$.',
  note: 'Новая лемма шага 13: Proper phi -> riemann_sum (fun x => phi (c*x+d) * c) a step n == riemann_sum phi (c*a+d) (c*step) n. Closed under the global context.' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part05-ch06.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
