// Часть V, шаг 7 (2026-11-12, слово автора «идём к шагу 7»): глава V.1, строки 1, 2, 5 таблицы — слова главы стали
// верны после доведения формализации; числа о MetricSpace.v на странице устарели (ждут правки слов).
// Записи, зависящие от правки слов (строки 3 и 4, числа, имена QVec), правит patch-p5-step-07-pages.cjs.
// Запуск: node patch-p5-step-07.cjs   (затем tom-links.cjs merge по ведомостям глав V.1 и V.2)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 7, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part05-ch01.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0;
function set(prefix, fields) {
  const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  Object.assign(hit[0], fields); n++;
}
set('все семь по своим заголовкам и проверенным ключевым теоремам имеют статус', {
  verdict: 'ok',
  note: DONE + ' — слова те же, доведена формализация: у stdlib/ProcessSpace.v шапка была одной строкой без статуса; теперь стандартная шапка E/R/R со строкой «STATUS: 6 Qed, 0 Admitted, 0 axioms» (и вписанный счёт process_space_count исправлен с 7 на 6). Цена всех семи файлов по компилятору — Closed under the global context.' });
set('Семь *основных* опорных файлов Главы 5.1 в своих шапках заявляют статус', {
  verdict: 'ok',
  note: DONE + ' — слова те же: седьмой файл, stdlib/ProcessSpace.v, получил шапку со статусом (см. запись к § 1.1).' });
set('рамка же берёт ровно те гипотезы, которые нужны для общих рассуждений', {
  verdict: 'ok',
  note: DONE + ' — слова те же, доведена формализация: гипотеза d_zero не входила ни в одну лемму секции; добавлены const_limit_metric и const_cauchy_metric (постоянная последовательность сходится к своему значению и есть Коши) — после закрытия секции обе зависят ровно от d_zero. Closed under the global context.' });
set('секция честно берёт ровно те гипотезы, которые работают', {
  verdict: 'ok',
  note: DONE + ' — слова те же: теперь работают все четыре гипотезы секции (d_nonneg, d_sym, d_triangle — в прежних леммах; d_zero — в const_limit_metric и const_cauchy_metric).' });
set('`MetricSpace.v` несёт восемнадцать проверенных лемм', {
  verdict: 'wrong-number',
  note: 'После шага 7 Части V (12.11) в файле 24 Qed, в абстрактной секции девять лемм (добавлены const_limit_metric, const_cauchy_metric и четыре леммы о QVec_dist); на странице — прежние «восемнадцать» и «семь». Правка слов показана автору.' });
set('Абстрактная метрическая рамка: метрическое пространство как параметрическая `Section`', {
  verdict: 'wrong-number',
  note: 'После шага 7 Части V (12.11) в MetricSpace.v 24 Qed; на странице — «восемнадцать проверенных результатов». Правка слов показана автору.' });
set('*$L^\\infty$-метрику на рациональных векторах* `QVec`', {
  verdict: 'ok',
  note: DONE + ' — слова те же, доведена формализация: четыре свойства были доказаны только для списков (треугольник — при равных длинах); добавлены QVec_dist_nonneg, QVec_dist_zero, QVec_dist_sym, QVec_dist_triangle — для самого расстояния на QVec n, треугольник без условия (длины равны по построению, qv_length). Closed under the global context.' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part05-ch01.json: записей изменено ' + n + ', всего ' + j.records.length);
