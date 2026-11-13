// Часть X, первая вычитка (2026-11-12): запись сверки 12.11 по главе X.6, оставленная «не проверено»
// (строка таблицы «| classic (L3) | Хигман; конечная детерминированность |»), получает вердикт.
// Запуск: node patch-p10-step-00.cjs   (затем tom-links.cjs merge ведомости/sverka-2026-11-12/X-6.json)
const fs = require('fs');
const path = require('path');
const p = path.join(__dirname, 'sverka-2026-11-12', 'X-6.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
const hit = j.records.filter((r) => (r.claim || '').startsWith('| classic (L3) | Хигман; конечная детерминированность |'));
if (hit.length !== 1) throw new Error('ожидалась одна запись, найдено ' + hit.length);
Object.assign(hit[0], {
  theorem: 'higman_synthesis',
  file: 'src/settheory/HigmanLemma.v',
  verdict: 'mismatch-price',
  note: 'Проверено при аудите Части X (12.11). higman_synthesis — Classical_Prop.classic; weak_determinacy и zero_game_determined (settheory/BorelDeterminacy.v) — BorelDeterminacy.classic: для итоговых теорем ярус верен. Но сама лемма Хигмана в доказанном объёме (higman_unit, однобуквенный алфавит) — Closed under the global context; classic приходит в higman_synthesis только через dickson_pair (лемма Диксона для пар). Слово «Хигман» в ярусе classic относится к конъюнкции, а не к лемме Хигмана. См. ведомость part10-ch06, расхождение 6.',
});
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('X-6.json: запись «Хигман; конечная детерминированность» — mismatch-price');
