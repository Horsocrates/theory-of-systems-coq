// Шаг 6 Части X, место 12: страница «Формализация», абзац о допущениях. Два фрагмента одной строки:
//   (а) снимается устаревшая оговорка о функциональной экстенсиональности (убрана из формализации 12.11);
//   (б) «три абстрактных параметра … и eval_program» -> «два абстрактных параметра» (eval_program стал
//       переменной раздела 13.11).
// Вносится точной заменой ОТДЕЛЬНО в страницу сайта и в её копию в репозитории (копии различаются одним
// посторонним словом, файл целиком не копируется).
// Запуск: node apply-step-06-formalizaciya.cjs [--dry]
const fs = require('fs');
const dry = process.argv.includes('--dry');
const FILES = [
  'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/Формализация.md',
  'C:/Users/abary/OneDrive/Desktop/theory-of-systems-coq/site/quartz/content/Библиотека/Формализация.md',
];
const PAIRS = [
  ['на которые результаты этой страницы не опираются: функциональная экстенсиональность стандартной библиотеки — в пяти файлах (Ordinal.v, DependentSystems.v, Conversion.v, ProcessWholeness.v, GameTheory.v); две аксиомы раздела Навье — Стокса',
   'на которые результаты этой страницы не опираются: две аксиомы раздела Навье — Стокса'],
  ['три абстрактных параметра — `C_B` и `B_raw`, о которых говорят только эти две аксиомы, и `eval_program`.',
   'два абстрактных параметра — `C_B` и `B_raw`, о которых говорят только эти две аксиомы.'],
];
for (const p of FILES) {
  let raw = fs.readFileSync(p, 'utf8');
  for (const [a, b] of PAIRS) {
    const k = raw.split(a).length - 1;
    if (k === 0 && raw.includes(b)) { console.log('уже внесено: ' + b.slice(0, 40) + '…'); continue; }
    if (k !== 1) throw new Error(p + ': фрагмент найден ' + k + ' раз(а): ' + a.slice(0, 60));
    raw = raw.replace(a, () => b);
  }
  if (!dry) fs.writeFileSync(p, raw);
  console.log((dry ? 'проверка: ' : 'внесено: ') + p);
}
