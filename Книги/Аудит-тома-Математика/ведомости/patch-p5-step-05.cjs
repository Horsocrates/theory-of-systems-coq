// Часть V, шаг 5 (2026-11-12, слово автора «идём к шагу 5»): теоремы-вывески пяти процессных файлов получили
// настоящие заключения. Здесь — записи, слова которых на страницах менять не нужно (они стали верны) или которые
// были верны и раньше (меняется только пометка о формулировке). Записи, зависящие от правки слов (V.2 стр. 879,
// V.3 стр. 995), правит patch-p5-step-05-pages.cjs — после слова автора о страницах.
// Запуск: node patch-p5-step-05.cjs   (затем tom-links.cjs merge по ведомостям глав V.2–V.6 и IV.1)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 5, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function patch(name, edits) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  for (const [prefix, fields] of edits) {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
    if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
    Object.assign(hit[0], fields);
  }
  fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
  console.log(name + ': записей изменено ' + edits.length + ', всего ' + j.records.length);
}
patch('part05-ch02.json', [
  ['Теорема `bw_is_process_construction` собирает это в единую', {
    verdict: 'ok',
    note: DONE + ' — слова те же, доведена формализация: теорема теперь говорит о самих процессах концов (bw_left_process s a b, bw_right_process s a b): монотонны, оба Коши, эквивалентны, и для каждого n infinitely_many_in s (левый конец n) (правый конец n). Раньше оба процесса стояли под «существует» и с последовательностью связаны не были (заключение выполнялось для пары нулевых процессов). Допущения те же, что у леммы о бисекции: classic и L4_witness.' }],
]);
patch('part05-ch04.json', [
  ['`derivative_is_process_construction` (производная предъявляется как Коши-процесс', {
    verdict: 'ok',
    note: DONE + ' — слова те же, доведена формализация: has_derivative f x L -> (forall n, deriv_process f x n == (f (x + deriv_step n) - f x) / deriv_step n) /\\ is_Cauchy (deriv_process f x) /\\ process_equiv (deriv_process f x) (const_process L). Раньше процесс стоял под «существует», и заключение выполнялось для const_process L без посылки. Closed under the global context.' }],
]);
patch('part05-ch05.json', [
  ['Теорема `integral_is_process_construction`, предъявляющая процесс', {
    note: 'Слова главы честны и до, и после шага 5 («не теорема интегрируемости»). Формулировка доведена 12.11 (Часть V, шаг 5): a < b -> (стадия n есть riemann_sum f a (integral_step a b n) (S n)) /\\ (шаг положителен) /\\ ((n+1) шагов дают b - a) /\\ (шаг в конце концов меньше любого delta — новая лемма integral_step_eventually_small). Раньше стояло одно первое условие под «существует», посылка a < b не использовалась. Closed under the global context.' }],
  ['интеграл как *процесс* накопления `integral_process`', {
    note: 'Все три объявления существуют. integral_is_process_construction после шага 5 Части V — «паспорт сетки» (стадия, положительность шага, точное покрытие отрезка, стремление шага к нулю); теоремой интегрируемости она по-прежнему не является — см. запись к § 5.1.' }],
]);
patch('part05-ch06.json', [
  ['Теорема `ftc_is_process_construction` предъявляет этот процесс ошибки', {
    note: 'Формулировка доведена 12.11 (Часть V, шаг 5): Proper f -> udiff_on f f\' a b -> (стадия процесса ошибки) /\\ is_Cauchy (integral_process f\' a b) /\\ process_equiv (integral_process f\' a b) (const_process (f b - f a)) /\\ process_equiv (ftc_error_process f f\' a b) (const_process 0). Раньше — одно первое условие под «существует», верное по определению, с неиспользуемой посылкой a < b. Теорема перенесена в конец файла (после раздела о сходимости). Closed under the global context.' }],
  ['процессная обёртка `ftc_error_process`, `ftc_is_process_construction`;', {
    note: 'Оба объявления существуют; ftc_is_process_construction после шага 5 Части V собирает определение процесса ошибки, свойство Коши процесса сумм и обе эквивалентности (см. запись к § 6.1).' }],
]);
