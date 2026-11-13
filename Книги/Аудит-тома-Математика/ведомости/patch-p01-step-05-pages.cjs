// Часть I, шаг 5, страницы (2026-11-13, слово автора «Делай»): 17 правок главы I.4 (места 1–8) внесены;
// формализация — src/foundation/PrinciplesFromLawsDerived.v.
// Запуск: node patch-p01-step-05-pages.cjs   (затем relocate + merge по part01-ch04)
// Скрипт повторяем: приведённая запись пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть I, шаг 5, слово автора)';
const F = 'src/foundation/';
const CD = F + 'DistinctionCoDefinition.v';
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

// ---- место 1
const OLD39 = 'Звенья $\\text{Distinction} \\to L1$–$L5$ и $L1$–$L5 \\to P1$–$P4$ суть формальные теоремы Rocq';
const NEW39 = 'Звенья $\\text{Distinction} \\to L1$–$L5$ и $L1$–$L5 \\to P1$–$P4$ записаны теоремами Rocq (файлы `LawsFromDistinction.v` и `PrinciplesFromLaws.v`), и записаны по-разному.';
a.fix(OLD39, 'five_laws_from_distinction', { claim: NEW39 }, true);
a.fix(OLD39, 'four_principles_from_five_laws', { claim: NEW39,
  note: DONE + ': было «суть формальные теоремы Rocq». Теоремы PrinciplesFromLaws.v утверждают сами принципы, законов в посылках нет; страница теперь говорит это, а для P1 вывод из L1 и L5 записан теоремой с посылками (P1_from_L1_and_L5).' });
const P1C = 'Этот шаг записан теоремой, в которой оба закона стоят посылками: если у системы один уровень ($L1$), порядок уровней иррефлексивен и организуемое лежит ниже организатора ($L5$), то ни одна система не организуется собой (`P1_from_L1_and_L5`); без каждой из двух посылок вывод не проходит (`P1_needs_L1`, `P1_needs_L5`).';
a.add({ theorem: 'P1_from_L1_and_L5', file: PD, claim: P1C,
  note: 'P1_from_L1_and_L5 : L1_determinate_level -> L5_irreflexive -> L5_organized_below -> forall x, ~ mem x x (абстрактные носители U, Lv, lt, at_level, mem). ' + CL + '. На типе Level: no_self_membership_Level.' });
a.add({ theorem: 'P1_needs_L1', file: PD, claim: P1C, note: 'Модель, в которой L5 выполнен в обеих формах, а система содержит себя (у системы два уровня). ' + CL + '.' });
a.add({ theorem: 'P1_needs_L5', file: PD, claim: P1C, note: 'Модель, в которой L1 выполнен, порядок рефлексивен, и система содержит себя. ' + CL + '.' });
a.fix('Формализация четырёх принципов и их деривация от законов содержится', null, {
  claim: 'Формализация четырёх принципов содержится в файле `PrinciplesFromLaws.v` репозитория ToS-Coq; доказательства опираются на `TheoryOfSystems_Core_ERR.v`.',
  note: DONE + ': было «и их деривация от законов… файл опирается на Distinction.v, LawsFromDistinction.v». Два названных файла подключены, но в доказательствах не участвуют.' });
a.fix('Также присутствует теорема `derivation_chain`, явно указывающая закон-источник', 'derivation_chain', {
  claim: 'Теорема `derivation_chain` повторяет её утверждение; закон-источник каждого принципа ($P1$ от $L1 + L5$; $P2$ от $L5$; $P3$ от $L1 + L4$; $P4$ от $L5$) указан в комментариях, в само утверждение он не входит.',
  note: DONE + ': было «явно указывающая закон-источник для каждого принципа». derivation_chain доказана строкой exact four_principles_from_five_laws.' });

// ---- место 7 (первое место, стр. 42–45)
a.fix('Завершающее же звено разобрано в файле `ERRFromDistinction.v`, и этот файл фиксирует', null, {
  claim: 'Завершающее же звено разобрано в файле `ERRFromDistinction.v`, и этот файл фиксирует более *узкое* ядро цепи, чем полная архитектурная схема: он размечает запись `Distinction` по трём аспектам — элементы, роли, правила, — не проводя',
  note: DONE + ': было «он выводит E/R/R-структуру прямо из записи Distinction и законов». В файле список сторон err_elements, три счётчика-определения и законы под именами аспектов; объекта «E/R/R-структура» нет.' });

// ---- место 2
a.fix('Законы $L1$–$L5$, выведенные в Главе 3, суть условия определённости', 'Law_of_ExcludedMiddle', {
  claim: 'Законы $L1$–$L5$, прослеженные в Главе 3 в записи `Distinction`, суть условия определённости в их самом общем виде.',
  note: DONE + ': было «выведенные в Главе 3». L3 для произвольной пропозиции — аксиома classic.' });
a.fix('Это — условия самой возможности системности, выводимые из деривационной цепи', 'classic', {
  claim: 'Это — условия самой возможности системности, выводимые из деривационной цепи и зафиксированные в Главе 3 в формализации Rocq: $L1$, $L2$, $L4$, $L5$ — теоремами, $L3$ — аксиомой `classic` и полем `exhaustive` записи `Distinction`.',
  note: DONE + ': было «как формальные теоремы Rocq».' });

// ---- место 3 (сноска 3)
const FN3 = 'Этот результат записан теоремами, в утверждение которых входит отношение принадлежности: если принадлежность понижает уровень, то условие Рассела «$x$ не содержит себя» выполнено для всего (`russell_condition_holds_everywhere`), собирателя этого условия по всему универсуму нет (`no_russell_collector`), а собиратель, взятый по уровням ниже своего, существует без противоречия (`levelled_collector_is_harmless`); все три — без аксиом, файл `PrinciplesFromLawsDerived.v`.';
a.fix('Этот результат зафиксирован в теореме `P1_blocks_russell`.', 'P1_blocks_russell', {
  claim: 'Теорема `P1_blocks_russell` повторяет иррефлексивность порядка уровней.',
  note: DONE + ': было «Этот результат зафиксирован в теореме P1_blocks_russell». P1_blocks_russell : forall l : Level, ~ (l << l) — то же утверждение, что P1_from_L1_L5; результат о принадлежности теперь записан тремя новыми теоремами.' });
a.add({ theorem: 'russell_condition_holds_everywhere', file: PD, page_price: 'без аксиом', claim: FN3,
  note: 'При посылке mem_lowers : forall x y, mem x y -> lev x << lev y: forall x, ~ mem x x. ' + CL + '.' });
a.add({ theorem: 'no_russell_collector', file: PD, page_price: 'без аксиом', claim: FN3,
  note: 'forall r, ~ (forall x, mem x r <-> ~ mem x x). ' + CL + '.' });
a.add({ theorem: 'levelled_collector_is_harmless', file: PD, page_price: 'без аксиом', claim: FN3,
  note: 'Собиратель по уровням ниже своего не содержит себя и содержит всё, что ниже. ' + CL + '.' });

// ---- место 4
a.fix('Иначе говоря: «$S$ есть то, что удовлетворяет $S$» — формулировка, заблокированная', 'P2_no_circularity', {
  claim: 'Иначе говоря: метка уровня критерия не может совпасть с уровнем системы.',
  note: DONE + ': было «формулировка, заблокированная самой типовой системой Rocq, поскольку требует построить критерий, нарушающий P2». P2_no_circularity запрещает совпадение метки уровня; о содержании критерия она не говорит — это теперь сказано следом.' });
a.add({ theorem: 'level_label_is_free', file: PD, claim: 'Сама по себе эта метка с содержанием критерия не связана (`level_label_is_free`);',
  note: 'level_label_is_free : l << L -> exists C : Criterion L, crit_domain L C = D /\\ crit_level_witness L C = l. ' + CL + '.' });
const LC = 'для критерия, уровень которого связан с содержанием — всё, что ему удовлетворяет, лежит ниже его уровня, — формулировка «$S$ есть то, что удовлетворяет $S$» исключена теоремой (`LevelledCriterion`, `levelled_membership_no_self`).';
a.add({ theorem: 'LevelledCriterion', file: PD, claim: LC, note: 'Record LevelledCriterion (L : Level) := { lc_pred : U -> Prop; lc_below : forall x, lc_pred x -> lev x << L }.' });
a.add({ theorem: 'levelled_membership_no_self', file: PD, claim: LC,
  note: 'levelled_membership_no_self : forall crit s, ~ lc_pred (lev s) (crit s) s. ' + CL + '.' });

// ---- место 5
const P3C = 'четвёртая раскрывает определение: интенсиональное равенство систем есть совпадение трёх полей записи `System` — критерия, границы позиций и ограничения единственности, — то есть равенство самих записей (`intensional_iff_eq`).';
a.fix('четвёртая фиксирует содержательное условие: совпадение трёх компонент', 'P3_from_L1_L4', { claim: P3C,
  note: DONE + ': было «совпадение трёх компонент критерия влечёт интенсиональное равенство систем». Посылки теоремы — равенства трёх полей записи System; заключение — их конъюнкция.' });
a.add({ theorem: 'intensional_iff_eq', file: PD, claim: P3C,
  note: 'intensional_iff_eq : systems_intensionally_equal S1 S2 <-> S1 = S2. ' + CL + '. Одного совпадения критерия мало: same_criterion_not_enough.' });

// ---- место 6
a.fix('Theorem P4_from_L5 : forall (R : nat -> Q) (n : nat), exists q : Q, R n = q.', 'P4_from_L5', {
  claim: 'Theorem P4_from_L5 : forall (R : nat -> Q) (n : nat), (exists (num : Z) (den : positive), R n = num # den) /\\ (n = 0%nat \\/ exists m : nat, n = S m).',
  note: DONE + ': блок кода приведён к нынешней формулировке (PrinciplesFromLaws.v:191, с июня 2026 г.); в исходнике тип знаменателя записан BinNums.positive.' });
a.fix('(forall (R : nat -> Q) n, exists q : Q, R n = q). (* P4 *)', 'four_principles_from_five_laws', {
  claim: '(forall (R : nat -> Q) n, exists (num : Z) (den : positive), R n = num # den). (* P4 *)',
  note: DONE + ': четвёртый член приведён к нынешней формулировке (PrinciplesFromLaws.v:251).' });

// ---- место 7
a.fix('Теорема `complete_foundation` из файла `ERRFromDistinction.v`[^5] доказывает следующее', 'complete_foundation', {
  page_price: 'classic',
  claim: 'Теорема `complete_foundation` из файла `ERRFromDistinction.v`[^5] доказывает следующее: из любой пропозиции строится `Distinction` (на аксиоме `classic`); для всякой `Distinction` выполнены законы $L2$ и $L3$ — это её поля `exclusive` и `exhaustive`; число ролей, заданное определением `err_role_count`, не меньше двух; и уровневая иерархия иррефлексивна.',
  note: DONE + ': было «всякая Distinction даёт E/R/R-структуру не менее чем с двумя ролями»; цена названа. Print Assumptions complete_foundation: Distinction.classic.' });
const CF = 'Третий член с содержанием — две стороны всякого различения различны, список сторон не имеет повторов и имеет длину два — доказан отдельно (`complete_foundation_with_sides`; без первого члена — `foundation_core_closed`, без аксиом).';
a.add({ theorem: 'complete_foundation_with_sides', file: PD, page_price: 'classic (первый член)', claim: CF,
  note: 'Print Assumptions: Distinction.classic — первый член строит различение для всякой пропозиции.' });
a.add({ theorem: 'foundation_core_closed', file: PD, page_price: 'без аксиом', claim: CF, note: CL + '.' });
a.fix('В Rocq двойственность зафиксирована числовыми инвариантами:[^7]', 'err_role_count', {
  claim: 'В Rocq двойственность записана определениями и доказана теоремами.[^7] Определениями — для всякой $D : \\texttt{Distinction}$:',
  note: DONE + ': было «зафиксирована числовыми инвариантами». Счётчики err_*_count — постоянные функции (err_role_count_constant); теоремы о «двух» названы следом.' });
const TWO = 'Теоремами, без аксиом: стороны всякого различения различны, список сторон не имеет повторов и имеет длину два (`sides_distinct`, `two_distinct_elements`); при любой разметке сторон позициями позиция выделенного и позиция фона различны — одной позиции недостаточно, двух достаточно (`two_positions_needed`, `one_position_insufficient`, `side_of_injective`); два правила записи независимы, и без каждого из них стороны могут совпасть (`exclusive_not_from_exhaustive`, `exhaustive_not_from_exclusive`, `without_exclusive_sides_may_coincide`, `without_exhaustive_sides_may_coincide`).';
for (const [th, file] of [['sides_distinct', CD], ['two_distinct_elements', PD], ['two_positions_needed', PD], ['one_position_insufficient', PD],
  ['side_of_injective', PD], ['exclusive_not_from_exhaustive', CD], ['exhaustive_not_from_exclusive', CD],
  ['without_exclusive_sides_may_coincide', PD], ['without_exhaustive_sides_may_coincide', PD]])
  a.add({ theorem: th, file, page_price: 'без аксиом', claim: TWO, note: CL + '.' });
a.fix('Соответствующие функции файла `ERRFromDistinction.v` — `err_element_count`, `err_role_count`, `err_rule_count`.', 'err_element_count', {
  claim: 'Соответствующие функции файла `ERRFromDistinction.v` — `err_element_count`, `err_role_count`, `err_rule_count`; каждая определена как число $2$ и от $D$ не зависит, так что три равенства верны по определению' }, true);
const FN7 = 'теоремы `distinction_has_two_roles` и `minimum_two_roles` это определение раскрывают; `distinction_has_two_elements` говорит о длине списка сторон';
const OLD7 = 'Также присутствуют теоремы `distinction_has_two_elements`, `distinction_has_two_roles`, `minimum_two_roles`, доказывающие эти равенства.';
for (const th of ['distinction_has_two_elements', 'distinction_has_two_roles', 'minimum_two_roles'])
  a.fix(OLD7, th, { claim: FN7, note: DONE + ': было «теоремы…, доказывающие эти равенства». ' + th + ' — ' + CL + '.' });

// ---- место 8 (сноска 10)
a.fix('Формальный аппарат — в файле `FormationRules.v`, опирающемся на тип `System`, поле `sys_criterion` (конкретный критерий системы), отношение `HasType`', 'HasType', {
  claim: 'Формальный аппарат — в файле `FormationRules.v`, опирающемся на тип `System`, поле `sys_criterion` (конкретный критерий системы) и суждение `HasType` из `Judgments.v`: контекст правилен и уровень критерия системы ниже её уровня.',
  note: DONE + ': было «отношение HasType (типизация системы в контексте)». Definition HasType (G) (S) := ctx_well_formed G /\\ crit_level_witness L (sys_criterion L S) << L (Judgments.v:150).' });
a.add({ theorem: 'HasType_iff_ctx', file: PD,
  claim: 'Второе условие выполнено для всякой системы по построению записи `Criterion`, так что `HasType` равносильно правильности контекста (`HasType_iff_ctx`).',
  note: 'HasType_iff_ctx : HasType L G S <-> ctx_well_formed G. ' + CL + '.' });
const OLD10 = 'Ключевые леммы — `sys_form` (правило формации системы), `p1_check` (проверка иерархии)';
const NEW10 = 'Леммы `sys_form`, `p1_check`, `l4_role_principle`, `wf4_check` раскрывают это определение: `sys_form` собирает суждение из двух условий, `p1_check` и `l4_role_principle` извлекают условие об уровне критерия (в двух записях), `wf4_check` — оба условия.';
a.fix(OLD10, 'sys_form', { claim: NEW10 }, true);
for (const th of ['p1_check', 'l4_role_principle', 'wf4_check'])
  a.fix(OLD10, th, { claim: NEW10, note: DONE + ': было — «проверка иерархии», «проверка обоснованности ролей», «общая проверка хорошей сформированности». Заключения p1_check и l4_role_principle верны без посылки и совпадают по определению (p1_check_without_premise, l4_role_principle_is_p1_check); заключение wf4_check совпадает с её посылкой (wf4_check_is_identity).' });
a.save();
