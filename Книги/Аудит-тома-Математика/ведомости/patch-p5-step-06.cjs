// Часть V, шаг 6 (2026-11-12, слово автора «А — снимаем, вносим три места»): «темпы сходимости», вписанные числом.
// Запуск: node patch-p5-step-06.cjs   (затем tom-links.cjs relocate + merge по ведомостям глав V.2–V.6, IV.1)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 6, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  return {
    set(prefix, fields) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
      Object.assign(hit[0], fields); n++;
    },
    add(rec) {
      if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); },
  };
}
const a = open('part05-ch02.json');
a.set('а `bw_convergence_rate` фиксирует скорость', {
  claim: 'а `bw_convergence_rate` фиксирует скорость — $1/2$: интервал на каждом шаге уполовинивается (лемма `bw_rate_is_width_ratio`).',
  verdict: 'ok',
  note: DONE + ': было — число, вписанное определением, с процессом не связанное (единственная лемма bw_rate_valid: 0 < 1/2 < 1). Добавлена связка bw_rate_is_width_ratio; само уполовинивание доказано в BolzanoWeierstrass.v (bw_step_width).' });
a.add({ theorem: 'bw_rate_is_width_ratio', file: 'src/process/ProcessBW.v',
  claim: 'интервал на каждом шаге уполовинивается (лемма `bw_rate_is_width_ratio`)',
  note: 'Новая лемма шага 6: bw_right_process s a b (S n) - bw_left_process s a b (S n) == bw_convergence_rate * (bw_right_process s a b n - bw_left_process s a b n). Допущения — classic и L4_witness (от bw_step в формулировке).' });
a.save();

const b = open('part05-ch03.json');
b.set('а `ivt_convergence_rate` фиксирует темп', {
  claim: 'а `ivt_convergence_rate` фиксирует темп — $1/2$: ширина интервала бисекции на каждом шаге уполовинивается (лемма `ivt_rate_is_width_ratio`).',
  verdict: 'ok',
  note: DONE + ': было сомнительное место — число записано определением, а связывала его с бисекцией только соседняя bisection_width_bound. Добавлена связка ivt_rate_is_width_ratio (ширина на стадии n+1 равна ivt_convergence_rate * ширина на стадии n); Closed under the global context.' });
b.set('Всё это — содержание файла `ProcessIVT.v` (175 строк).', {
  claim: 'содержание файла `ProcessIVT.v` (190 строк).',
  note: DONE + ': после шага 6 в файле 190 строк, 14 Qed, 0 Admitted (было 175 строк, 13 Qed).' });
b.set('Третий файл — `ProcessEVT.v` (158 строк)', {
  claim: 'Третий файл — `ProcessEVT.v` (190 строк)',
  note: DONE + ': после шага 6 в файле 190 строк, 10 Qed (после шага 5 было 158 строк, 9 Qed; до него на странице стояло «133 строки» при 137).' });
b.set('`evt_convergence_rate` фиксирует темп', {
  theorem: 'evt_lipschitz_rate', file: 'src/process/ProcessEVT.v',
  claim: 'Темп называет теорема `evt_lipschitz_rate`: для функции с константой Липшица $K$ значение на $n$-й сетке отстоит от любого значения функции на отрезке не больше чем на $K(b-a)/(n+1)$.',
  verdict: 'ok',
  note: DONE + ': было «evt_convergence_rate фиксирует темп — 1/2» — число, вписанное определением; для сетки, получающей одну ячейку на стадию, такого темпа нет (отклонение для x(1-x) на [0,1]: 1/36, 1/100, 1/196, …). Определение evt_convergence_rate и лемма evt_rate_valid сняты (вариант А, слово автора); на их месте evt_lipschitz_rate : a < b -> a <= x <= b -> 0 <= K -> (условие Липшица на отрезке) -> f x <= sup_process f a b n + K * ((b - a) / (n+1)). Closed under the global context. Строка шапки файла «doubling points at each step» заменена на «one more cell at each stage, keep the max».' });
b.add({ theorem: 'ivt_rate_is_width_ratio', file: 'src/process/ProcessIVT.v',
  claim: 'ширина интервала бисекции на каждом шаге уполовинивается (лемма `ivt_rate_is_width_ratio`)',
  note: 'Новая лемма шага 6: bis_right (bisection_iter f (mkBisection a b) (S n)) - bis_left (…(S n)) == ivt_convergence_rate * (bis_right (… n) - bis_left (… n)); из bisection_width и Qpow2_Sn. Closed under the global context.' });
b.add({ theorem: 'evt_step_halves_on_doubling', file: 'src/process/ProcessEVT.v',
  claim: '$1/2$ появляется лишь при удвоении числа ячеек (`evt_step_halves_on_doubling`).',
  note: 'Новая лемма шага 6: (b - a) / (2n+2) == (1 # 2) * ((b - a) / (n+1)) — шаг сетки стадии 2n+1 вдвое меньше шага стадии n. Closed under the global context.' });
b.save();
