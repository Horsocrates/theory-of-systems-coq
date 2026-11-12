// Шаг 9 (2026-11-12, слово автора «А — доказываем обратную сторону»): глава IV.3, сноска 2 — поле апартности.
// Запуск: node patch-step-09.cjs   (затем tom-links.cjs relocate + merge)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (шаг 9, слово автора «А»)';
const F = 'src/RealFieldApart.v';
const p = path.join(__dirname, 'part04-ch03.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0;
function one(prefix) {
  const hit = j.records.filter((r) => (r.claim || '').startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  return hit[0];
}
const rec = one('теорема `apart_has_inverse` даёт: обратный по умножению существует');
Object.assign(rec, {
  theorem: 'invertible_iff_apart', file: F,
  claim: 'теорема `invertible_iff_apart` даёт: обратный по умножению существует *в точности* для апартных от нуля элементов',
  verdict: 'ok',
  note: DONE + ' — правка формализации: в RealFieldApart.v доказана обратная сторона, inverse_implies_apart : cauchy_equiv (cauchy_mul x y) cauchy_one -> apart0 x (зазор 1/(2B) из границы обратного, cauchy_bounded), и invertible_iff_apart : apart0 x <-> exists y, cauchy_equiv (cauchy_mul x y) cauchy_one; Closed under the global context' }); n++;
const i = j.records.indexOf(rec);
const add = [
  { line: rec.line, theorem: 'apart_has_inverse', file: F, claim: 'в одну сторону — `apart_has_inverse`', page_price: '', verdict: 'ok',
    note: 'apart0 x -> exists y, cauchy_equiv (cauchy_mul x y) cauchy_one (RealFieldApart.v:103); Closed under the global context' },
  { line: rec.line, theorem: 'inverse_implies_apart', file: F, claim: 'в обратную — `inverse_implies_apart`', page_price: '', verdict: 'ok',
    note: DONE + ': теорема добавлена шагом 9; forall x y, cauchy_equiv (cauchy_mul x y) cauchy_one -> apart0 x; Closed under the global context' },
].filter((a) => !j.records.some((r) => r.claim === a.claim));
j.records.splice(i + 1, 0, ...add); n += add.length;
Object.assign(one('всё вместе — `apartness_field`'), {
  note: 'RealFieldApart.v — конъюнкция трёх: апартный в конце концов одного знака (apart0_sign); апартность равносильна обратимости (после шага 9 второй член — invertible_iff_apart, было: только apart_has_inverse); ~ apart0 0.' }); n++;
Object.assign(one('Машинно проверено, 6 Qed, 0 аксиом.'), {
  claim: 'Машинно проверено, 8 Qed, 0 аксиом.',
  note: DONE + ': было 6; после шага 9 в RealFieldApart.v 8 Qed, 0 Admitted; Print Assumptions для всех восьми — Closed under the global context.',
  assumptions: 'Closed under the global context (все 8 утверждений файла)' }); n++;
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part04-ch03.json: записей изменено или добавлено ' + n + ', всего ' + j.records.length);
