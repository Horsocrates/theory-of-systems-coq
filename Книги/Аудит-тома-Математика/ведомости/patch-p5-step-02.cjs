// Часть V, шаг 2 (2026-11-12, слово автора «Да — вносим»): основная теорема анализа как сходимость процесса.
// Записи ведомостей глав V.5 и V.6 о сходимости сумм производной приводятся к новым словам и новым теоремам.
// Запуск: node patch-p5-step-02.cjs   (затем tom-links.cjs relocate + merge по обеим ведомостям)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 2, слово автора)';
const NEWT = 'шагом 2 в формализацию добавлены ftc_grid_eventually (RiemannIntegration.v: оценка на всех уровнях начиная с некоторого) и ftc_process_converges, ftc_integral_process_Cauchy, ftc_error_process_vanishes (process/ProcessFTC.v; условие Proper (Qeq ==> Qeq) f); все — Closed under the global context';
const norm = (s) => (s || '').replace(/\s+/g, ' ');

function run(file, edits) {
  const p = path.join(__dirname, file);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0;
  for (const e of edits) {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(e.was));
    if (hit.length !== 1) throw new Error(file + ': ожидалась одна запись «' + e.was + '», найдено ' + hit.length);
    Object.assign(hit[0], e.set); n++;
  }
  fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
  console.log(file + ': записей изменено ' + n + ', всего ' + j.records.length);
}
const RI = 'src/RiemannIntegration.v', PF = 'src/process/ProcessFTC.v';

run('part05-ch05.json', [
  { was: 'равномерная дифференцируемость `udiff_on` из § 5.4 окажется', set: {
      theorem: 'ftc_process_converges', file: PF, verdict: 'ok',
      note: DONE + ' — слова главы не менялись, доведена формализация: ' + NEWT } },
  { was: 'Для констант это видно сразу', set: {
      theorem: 'ftc_integral_process_Cauchy', file: PF,
      claim: 'Для констант это видно сразу (§ 5.2.1); для производных равномерно дифференцируемых функций оно доказано — теоремой `ftc_integral_process_Cauchy`, из сеточной формы основной теоремы (§ 5.5).',
      verdict: 'ok',
      note: DONE + ': было «для более широких классов функций свойство Коши собирается из сеточных оценок и grid-формы основной теоремы»; ' + NEWT } },
  { was: 'Честная граница: отдельного предиката', set: {
      theorem: 'ftc_integral_process_Cauchy', file: PF,
      claim: 'Честная граница: отдельного предиката интегрируемости в ядре нет; свойство Коши доказано для двух классов — констант и производных равномерно дифференцируемых функций (§ 5.5.3).',
      verdict: 'ok',
      note: DONE + ': было «свойство Коши собирается из сеточных оценок для конкретного класса функций»; константы — integral_process_const (ProcessIntegral.v:64) и const_riemann_cauchy (ProcessSimple.v:85); производные — ftc_integral_process_Cauchy' } },
  { was: 'Это его *сеточная, приближённая* форма', set: {
      theorem: 'ftc_grid_eventually', file: RI, verdict: 'ok',
      note: DONE + ' — слова о «достаточно мелкой сетке» теперь покрыты теоремой ftc_grid_eventually (все уровни начиная с некоторого); следом на странице добавлена фраза о разнице между ftc_grid (один уровень) и ftc_grid_eventually' } },
  { was: 'Для некоторых достаточно регулярных', set: {
      theorem: 'ftc_process_converges', file: PF,
      claim: 'Для двух классов это доказано. Для констант — леммой `integral_process_const`. Для производной равномерно дифференцируемой функции — теоремой `ftc_process_converges`: процесс её Римановых сумм эквивалентен постоянному процессу приращения $f(b)-f(a)$ и потому есть процесс Коши (`ftc_integral_process_Cauchy`); условие — функция уважает равенство рациональных (§ 5.5.2).',
      verdict: 'ok',
      note: DONE + ': было «для некоторых достаточно регулярных классов это поведение уже поддержано сеточными оценками»; ' + NEWT } },
  { was: 'Есть сеточные оценки для конкретных', set: {
      claim: 'Есть теоремы для двух конкретных классов — констант и производных равномерно дифференцируемых функций.',
      verdict: 'ok',
      note: DONE + ': было «есть сеточные оценки…, из которых свойство Коши собирается для конкретной функции»; теоремы — integral_process_const и ftc_integral_process_Cauchy' } },
  { was: 'его законность как интеграла даёт', set: {
      claim: 'его законность как интеграла даёт сходимость — свойство Коши, которое доказано для констант и для производных равномерно дифференцируемых функций.',
      verdict: 'ok',
      note: DONE + ': было «для конкретных регулярных классов функций собирается из сеточных оценок»; теоремы — integral_process_const и ftc_integral_process_Cauchy' } },
]);

run('part05-ch06.json', [
  { was: 'Это *процессная обёртка*', set: {
      theorem: 'ftc_process_converges', file: PF,
      claim: 'Определения `ProcessFTC.v` записывают ошибку основной теоремы в процессной форме, а его теорема `ftc_process_converges` доказывает главное: процесс Римановых сумм производной эквивалентен постоянному процессу приращения $f(b)-f(a)$, то есть ошибка стремится к нулю (`ftc_error_process_vanishes`).',
      verdict: 'ok',
      note: DONE + ': было «Это процессная обёртка… сами по себе не доказывают, что эта ошибка убывает или образует процесс Коши»; ' + NEWT } },
  { was: 'Более того: хотя шапка', set: {
      theorem: 'ftc_grid_eventually', file: RI,
      claim: 'Сеточную оценку, на которой это стоит, даёт `RiemannIntegration.v`: лемма `ftc_grid` — для одного уровня сетки, теорема `ftc_grid_eventually` — для всех уровней начиная с некоторого.',
      verdict: 'ok',
      note: DONE + ': было «в доказательствах самого файла ftc_grid не вызывается»; теперь ftc_process_converges опирается на ftc_grid_eventually' } },
  { was: 'По $P4$ оба суть процессы приближений', set: {
      theorem: 'ftc_grid_eventually', file: RI, verdict: 'ok',
      note: DONE + ' — слова главы не менялись, доведена формализация: «оценки, уточняющиеся с измельчением» — ftc_grid_eventually (оценка держится на всех уровнях начиная с некоторого)' } },
  { was: 'форма *division-free*, *сеточная*, *приближённая*', set: {
      theorem: 'ftc_grid_eventually', file: RI, verdict: 'ok',
      note: DONE + ' — слова главы не менялись, доведена формализация: «при достаточно мелкой сетке» — ftc_grid_eventually' } },
  { was: 'Это та же интонация', set: {
      theorem: 'ftc_process_converges', file: PF,
      claim: 'Это та же интонация, что в § 5.4 с мостом `deriv_process_converges`: там процесс разностных отношений сходился к наклону, здесь процесс Римановых сумм производной сходится к приращению (`ftc_process_converges`).',
      verdict: 'ok',
      note: DONE + ': сходимость процесса теперь теорема — process_equiv (integral_process f\' a b) (const_process (f b - f a)); на странице добавлено её имя' } },
  { was: 'Чем мельче сетка', set: {
      theorem: 'ftc_error_process_vanishes', file: PF,
      claim: 'С измельчением сетки этот остаток стремится к нулю.',
      verdict: 'ok',
      note: DONE + ': было «Чем мельче сетка, тем меньше этот остаток» — доказана сходимость ошибки к нулю (ftc_error_process_vanishes), а не её убывание на каждом шаге' } },
  { was: '`ProcessFTC.v` — «', set: {
      claim: '12 Qed, 0 axioms',
      verdict: 'ok',
      note: DONE + ': было « 8 Qed, 0 axioms » при девяти; после шага 2 в ProcessFTC.v 12 Qed, шапка файла исправлена (строка 10 таблицы главы V.6 в отчёте 03)' } },
  { was: '`ftc_grid` назван в шапке', set: {
      claim: 'сходимость процесса в `ProcessFTC.v` доказана теоремой `ftc_process_converges` — через `ftc_grid_eventually`; теорема `derivative_integral_duality` содержит фиктивный процесс; `ftc_interval_split` не есть аддитивность; многие леммы `ProcessFTC.v` — переэкспорты уже доказанного.',
      note: DONE + ': первая часть фразы была «ftc_grid назван в шапке ProcessFTC.v среди правил, но в доказательствах файла не вызывается»; остальное без изменений' } },
  { was: 'Под $P4$ основная теорема анализа', set: {
      theorem: 'ftc_process_converges', file: PF,
      claim: 'Под $P4$ основная теорема анализа — не одна завершённая предельная идентичность $\\int_a^b f\' = f(b)-f(a)$, а *процессная связь*: семейство приближений, в котором на каждом уровне сетки Риманова сумма производной приближает приращение функции, а ошибка с измельчением стремится к нулю.',
      verdict: 'ok',
      note: DONE + ': было «а точность растёт с измельчением»; доказана сходимость (ftc_process_converges, ftc_error_process_vanishes), не убывание на каждом шаге' } },
]);
