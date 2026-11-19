// Поправка к шагу 1 Части VII: в сноске 4 главы VII.1 знак параграфа при сборке описания правок превратился в
// обратную косую черту («— \ «Конкретная…» вместо «— § «Конкретная…»): генератор шага 1 пропустил всю строку
// через замену «§ -> \». Восстанавливает знак. Запуск: node make-step-01a-spec.cjs -> шаг-01а-сноска-4-знак-параграфа.txt
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const REL1 = 'Направления/Математика/Том Математика/07 Гармонический анализ/01 Ортонормированные системы и коэффициенты Фурье.md';
const BS = String.fromCharCode(92);
const PAR = String.fromCharCode(167);   // знак параграфа
const page = fs.readFileSync(LIVE + REL1, 'utf8').replace(/\r/g, '').split('\n');
const hits = page.filter((l) => l.startsWith('[^4]: `Hypothesis Hon'));
if (hits.length !== 1) throw new Error('сноска 4 не найдена однозначно');
const bad = 'Адамара — ' + BS + ' «Конкретная';
if (hits[0].split(bad).length !== 2) throw new Error('испорченный фрагмент не найден (уже исправлено?)');
const neu = hits[0].replace(bad, () => 'Адамара — ' + PAR + ' «Конкретная');
fs.writeFileSync(path.join(__dirname, 'шаг-01а-сноска-4-знак-параграфа.txt'), ['@@FILE ' + REL1, '@@OLD', hits[0], '@@NEW', neu, '@@END'].join('\n') + '\n');
console.log('шаг-01а-сноска-4-знак-параграфа.txt: правок 1');
