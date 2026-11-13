// Часть I, шаг 6, страницы (2026-11-13, слово автора «А, делай»): вариант А развилки
// (every_distinction_err_well_formed — утверждение, в которое различение входит) и 9 правок главы I.4
// (места 9–11, 15, 18) внесены. Запуск: node patch-p01-step-06-pages.cjs (затем relocate + merge по part01-ch04)
// Скрипт повторяем: приведённая запись пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть I, шаг 6, слово автора)';
const F = 'src/foundation/';
const PD = F + 'PrinciplesFromLawsDerived.v';
const CL = 'Closed under the global context';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  return {
    fix(prefix, th, fields, keepVerdict) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) &&
        (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
      if (hit.length === 0) return;
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix.slice(0, 50) + '» / ' + th + ', найдено ' + hit.length);
      Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
    },
    add(rec) {
      if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); },
  };
}
const a = open('part01-ch04.json');
const L5N = 'L5_no_infinite_descent : forall l1 l2 : Level, l1 << l2 -> (level_depth l1 < level_depth l2)%nat (формулировка с июня 2026 г.). ' + CL + '.';

// ---- место 9
a.fix('Каждый конкретный уровень имеет конечную глубину относительно основания — это и фиксирует теорема', 'L5_no_infinite_descent', {
  claim: 'Каждый конкретный уровень имеет конечную глубину относительно основания: глубина задана функцией `level_depth` со значениями в натуральных числах. Теорема `L5_no_infinite_descent` из Главы 3 фиксирует большее — при спуске по $\\ll$ глубина строго убывает.',
  note: DONE + ': было «это и фиксирует теорема L5_no_infinite_descent» (о прежней формулировке). ' + L5N });
const REG = 'Поэтому отсутствие неоснованного нисхождения здесь не интерпретация, а теорема: бесконечной нисходящей цепи уровней нет (`no_infinite_level_regress`), порядок $\\ll$ фундирован (`level_lt_wf`).';
a.fix('но саму теорему о невозможности бесконечной нисходящей цепи уровней пришлось бы', 'no_infinite_level_regress', {
  claim: REG, file: F + 'MetaPairStrength.v', page_price: '',
  note: DONE + ': было «саму теорему… пришлось бы формулировать отдельно». no_infinite_level_regress : forall f : nat -> Level, ~ (forall n, level_lt (f (S n)) (f n)). ' + CL + '.' });
a.add({ theorem: 'level_lt_wf', file: F + 'MetaPairStrength.v', claim: REG,
  note: 'level_lt_wf : well_founded level_lt (то же — в TransfiniteInductionLevel.v). ' + CL + '.' });
a.fix('каждый уровень имеет конечную глубину; потому иерархия имеет', 'L5_no_infinite_descent', {
  claim: 'глубина уровня строго убывает при спуске, так что спуск от любого уровня конечен; потому иерархия имеет *нижнюю границу* — базовый уровень $L_1$.',
  note: DONE + ': было «каждый уровень имеет конечную глубину». ' + L5N });
a.fix('каждый *конкретный* уровень имеет конечную глубину относительно основания (это и есть содержание', 'L5_no_infinite_descent', {
  claim: 'каждый *конкретный* уровень имеет конечную глубину относительно основания, и при спуске она строго убывает (это и есть содержание $L5$ и теоремы `L5_no_infinite_descent`)',
  note: DONE + ': добавлено «и при спуске она строго убывает». ' + L5N });

// ---- место 10
a.fix('Их вывод в Rocq как теорем (Глава 3) — методологическое прослеживание', 'five_laws_from_distinction', {
  claim: 'Их запись в Rocq (Глава 3: $L2$ в общем виде — теорема без допущений; $L3$ для произвольной пропозиции — аксиома `classic`; в записи `Distinction` $L2$ и $L3$ даны полями `exclusive` и `exhaustive`) — методологическое прослеживание, не онтологическое основание.',
  note: DONE + ': было «Их вывод в Rocq как теорем (Глава 3)».' });
a.fix('формальный вывод законов из этой записи — в Главе 3.', 'five_laws_from_distinction', {
  claim: 'формальный разбор законов на этой записи — в Главе 3.', note: DONE + ': было «формальный вывод законов из этой записи».' });
a.fix('*Универсальный слой* — законы $L1$–$L5$. Они работают в `Distinction` как теоремы', 'L3_from_distinction', {
  claim: '*Универсальный слой* — законы $L1$–$L5$. В `Distinction` они записаны теоремами Главы 3; для $L2$ и $L3$ эти теоремы читают поля `exclusive` и `exhaustive`.',
  note: DONE + ': было «как теоремы, выведенные в Главе 3». L3_from_distinction читает поле exhaustive; ' + CL + '.' });

// ---- место 11
a.fix('было показано, что $L4$ *самообоснован* в формальной системе Rocq', 'L4_self_grounding', {
  claim: 'было показано, как $L4$ записан в Rocq: его формальная запись получена из самой записи различения, из поля `exclusive`, без обращения к чему-либо внешнему.',
  note: DONE + ': было «L4 самообоснован в формальной системе Rocq»; формула автора о самообосновании оставлена как содержательное прочтение. L4_self_grounding : forall D (p : positive D), ~ negative D — из поля exclusive; ' + CL + '. Отношения «быть основанием» между утверждениями в записи нет — горизонт.' });

// ---- место 15
a.fix('`every_distinction_err_well_formed` распространяет это на всякий такой разбор.', 'every_distinction_err_well_formed', {
  claim: '`every_distinction_err_well_formed` связывает таблицу со всяким различением: её компоненты-элементы суть две стороны данного $D$, а компоненты-правила — утверждения, истинные для $D$ по его полям `exclusive` и `exhaustive`.',
  note: DONE + ': вариант А развилки. С 13.11: every_distinction_err_well_formed : forall D, is_well_formed distinction_meta_system = true /\\ (distinction_content D 0 = positive D /\\ distinction_content D 1 = negative D) /\\ (forall i, errs_category distinction_meta_system i = Cat_Rule -> distinction_content D i). ' + CL + '. Прежняя формулировка (forall _ : Distinction, …) переменную не использовала и повторяла distinction_err_well_formed.' });

// ---- место 18 (сноска 20)
const FN20a = 'Само $P1$ записано в `PrinciplesFromLaws.v` («$P1$: иерархия») как иррефлексивность порядка уровней (`P1_from_L1_L5`; то же утверждение стоит там под именем `P1_blocks_russell`).';
const FN20b = 'Собственно о конструкции Рассела — теоремы с отношением принадлежности в файле `PrinciplesFromLawsDerived.v` (`no_russell_collector`, `levelled_collector_is_harmless`) и теоремы файла `TransfiniteInductionLevel.v`: `criterion_label_never_own_level` (метка уровня критерия не бывает его собственным уровнем) и `russell_blocked_every_level` (ни на каком уровне нет системы, собирающей в точности те системы этого уровня, что не принадлежат себе).';
a.fix('В `PrinciplesFromLaws.v` («$P1$: иерархия») есть также отдельная теорема `P1_blocks_russell`', 'P1_blocks_russell', {
  claim: FN20a, note: DONE + ': было «отдельная теорема P1_blocks_russell, фиксирующая, что P1 блокирует конструкцию Рассела». P1_blocks_russell : forall l : Level, ~ (l << l) — то же утверждение, что P1_from_L1_L5.' });
a.add({ theorem: 'P1_from_L1_L5', file: F + 'PrinciplesFromLaws.v', claim: FN20a, note: 'P1_from_L1_L5 : forall l : Level, ~ (l << l). ' + CL + '.' });
a.add({ theorem: 'no_russell_collector', file: PD, claim: FN20b, note: CL + '.' });
a.add({ theorem: 'levelled_collector_is_harmless', file: PD, claim: FN20b, note: CL + '.' });
a.add({ theorem: 'criterion_label_never_own_level', file: F + 'TransfiniteInductionLevel.v', claim: FN20b,
  note: 'criterion_label_never_own_level : forall (L : Level) (C : Criterion L), crit_level_witness L C <> L. ' + CL + '.' });
a.add({ theorem: 'russell_blocked_every_level', file: F + 'TransfiniteInductionLevel.v', claim: FN20b,
  note: 'russell_blocked_every_level : forall L mem, ~ exists R : System L, forall X, mem X R <-> ~ mem X X. ' + CL + '.' });
a.save();
