// Часть II, шаг 4, страницы (2026-11-13/14, слово автора «Вноси; А»): 14 правок главы II.3 и правка-развилка
// (А: блок двух лемм о восхождении заменён настоящими объявлениями, сноска 5 переписана) внесены.
// Формализация — новый src/foundation/LevelAscent.v; существующие MetaPairStrength.v, UniversePolymorphism.v,
// TransfiniteInductionLevel.v, LevelNatIso.v.
// Запуск: node patch-p02-step-04-pages.cjs  (затем relocate + merge по part02-ch03). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 14.11 (Часть II, шаг 4, слово автора)';
const F = 'src/foundation/';
const LA = F + 'LevelAscent.v';
const MP = F + 'MetaPairStrength.v';
const TI = F + 'TransfiniteInductionLevel.v';
const LN = F + 'LevelNatIso.v';
const L5 = F + 'L5_NatFromHierarchy.v';
const UP = 'src/UniversePolymorphism.v';
const CL = 'Closed under the global context';
const BS = String.fromCharCode(92);
const LL = '$' + BS + 'll$';
const TT = (s) => BS + 'texttt{' + s + '}';
const OR = BS + '/';
const AND = '/' + BS;
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

function open(name) {
  const p = path.join(__dirname, name + '.json');
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  const fix = (prefix, th, fields) => {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
    if (!hit.length) return;                                   // уже внесено
    if (hit.length !== 1) throw new Error(name + ': не одна запись: ' + prefix);
    Object.assign(hit[0], { verdict: 'ok' }, fields); n++;
  };
  const add = (rec) => {
    if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
    j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
  };
  const save = () => { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + '.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); };
  return { j, fix, add, save };
}

{
  const { fix, add, save } = open('part02-ch03');

  // --- § 3.3: конечность снизу
  fix('Такая теорема в иерархическом пути не используется и в процитированных файлах не доказана', 'no_infinite_level_regress', {
    claim: 'Такая теорема в иерархическом пути не используется; в репозитории она доказана отдельно — теоремой `no_infinite_level_regress` (файл `MetaPairStrength.v`), через убывание `level_depth` вдоль ' + LL + ' (см. ниже).[^1]',
    note: DONE + ': было «в процитированных файлах не доказана; понадобилась бы отдельная формализация». no_infinite_level_regress : forall f : nat -> Level, ~ (forall n, level_lt (f (S n)) (f n)) (MetaPairStrength.v:137, с 12.06.2026); ' + CL + '.' });
  fix('Прямую минимальность основания и открытость иерархии вверх удобно было бы выразить', 'L1_minimal', {
    claim: 'Прямая минимальность основания и открытость иерархии вверх выражены ещё двумя короткими леммами — $' + BS + 'neg (l ' + BS + 'll ' + TT('L1') + ')$ для всякого $l$ (ниже основания уровней нет) и $l ' + BS + 'll ' + TT('LS') + ' l$ (над всяким уровнем есть следующий); обе доказываются прямо из определения ' + LL + '.[^2]',
    note: DONE + ': было «удобно было бы выразить… их добавление в основной файл сделало бы опору прямой». L1_minimal : forall l, ~ (l << L1) (UniversePolymorphism.v:225); level_lt_LS : forall l, l << LS l (:74). ' + CL + '.' });
  fix('Бесконечный спуск от данного уровня невозможен — но это утверждение о каждом конкретном уровне', 'no_infinite_level_regress', {
    claim: 'Бесконечный спуск от данного уровня невозможен — это утверждение о каждом конкретном уровне; общая теорема о произвольных убывающих последовательностях доказана в репозитории отдельно, и путь на неё не опирается.',
    note: DONE + ': было «не общая теорема о произвольных убывающих последовательностях». Общая теорема — no_infinite_level_regress (MetaPairStrength.v:137); ' + CL + '.' });
  // --- § 3.4: лемма level_depth_LS
  fix('Lemma level_depth_LS : forall l,', 'level_depth_LS', { file: LA,
    note: DONE + ' (формализацией): лемма внесена дословно — ' + LA + '. Lemma level_depth_LS : forall l, level_depth (LS l) = S (level_depth l). Proof. reflexivity. Qed. ' + CL + '.' });
  fix('Лемма почти тривиальна — доказывается одним `reflexivity`', 'level_depth_LS', { file: LA,
    note: DONE + ' (формализацией): лемма есть в ' + LA + '; доказательство — reflexivity. ' + CL + '.' });
  add({ theorem: 'level_depth_LS', file: LA, claim: 'черта фиксируется простой леммой (файл `LevelAscent.v`):',
    note: 'Файл назван верно: лемма объявлена в ' + LA + ', § 1.' });
  // --- § 3.4: два слоя нумерации
  fix('В репозитории есть *две* функции, сопоставляющие уровню число', 'level_depth_eq', {
    claim: 'В репозитории есть *две* нумерации уровней, и они дают *разные* результаты для основания.',
    note: DONE + ': было «две функции». Нумераций две: с единицы (level_depth) и с нуля (level_to_nat — в отдельном файле и, на основном типе, в LevelNatIso.v). Связь: level_depth_eq : level_depth l = S (level_to_nat l) (LevelNatIso.v:121). ' + CL + '.' });
  fix('В отдельном файле `L5_NatFromHierarchy.v` функция `level_to_nat` сопоставляет базовому уровню *нуль*', 'level_to_nat', {
    claim: 'В отдельном файле `L5_NatFromHierarchy.v` функция `level_to_nat` сопоставляет базовому уровню *нуль*: там `level_to_nat LBase = 0`',
    note: 'Fixpoint level_to_nat (L5_NatFromHierarchy.v:17); peano_zero : level_to_nat LBase = O (:52). ' + CL + '.' });
  add({ theorem: 'level_to_nat', file: LN,
    claim: '(такая же нумерация с нуля есть и на основном типе — функция `level_to_nat` файла `LevelNatIso.v`).',
    note: 'Fixpoint level_to_nat (l : Level) : nat (LevelNatIso.v:37): L1 переходит в 0, LS — в S (level_to_nat_LS, :50).' });
  add({ theorem: 'level_depth_counts_from_one', file: LA,
    claim: 'Формально левый столбец сведён в одну теорему — `level_depth_counts_from_one` (файл `LevelAscent.v`): глубина есть взаимно однозначное соответствие уровней и *положительных* чисел, переводящее `L1` в $1$, `LS` в `S` и порядок ' + LL + ' в порядок чисел;',
    note: 'level_depth_counts_from_one : (forall l, 1 <= level_depth l) ' + AND + ' (forall l, level_of_depth (level_depth l) = l) ' + AND + ' (forall n, 1 <= n -> level_depth (level_of_depth n) = n) ' + AND + ' level_depth L1 = 1 ' + AND + ' (forall l, level_depth (LS l) = S (level_depth l)) ' + AND + ' (forall l1 l2, l1 << l2 <-> level_depth l1 < level_depth l2). ' + CL + '.' });
  add({ theorem: 'zero_is_not_a_depth', file: LA,
    claim: 'нуль глубиной не является (`zero_is_not_a_depth`).',
    note: 'zero_is_not_a_depth : forall l : Level, level_depth l <> 0. ' + CL + '.' });
  // --- § 3.4: изоморфизм — копия и основной тип
  fix('Но *технически* этот файл использует *собственную копию* типа уровней: он объявляет `Inductive Level := LBase | LSucc`', 'LBase', {
    claim: 'Но *технически* этот файл использует *собственную копию* типа уровней: он объявляет `Inductive Level : Set := LBase : Level | LSucc : Level -> Level` и не импортирует основной файл.',
    note: DONE + ': запись объявления приведена к исходнику (L5_NatFromHierarchy.v:13). Прежняя запись буквально задавала тип из двух констант.' });
  fix('Для полной синхронизации репозитория соответствующие леммы желательно перенести на основной тип', 'core_level_is_peano', {
    claim: 'Синхронизация проведена в файле `LevelNatIso.v`: он импортирует Core-определение и доказывает то же об основном типе `Level` — взаимную обратность отображений, переход `LS` в `S`, совпадение порядка ' + LL + ' с порядком чисел в обе стороны (сводная теорема `core_level_is_peano`), — а два типа уровней связывает явным изоморфизмом.',
    note: DONE + ': было «желательно перенести… до этого изоморфизм доказан для standalone-копии». Перенос сделан 12.06.2026: core_level_is_peano (LevelNatIso.v:150) — семь конъюнктов об основном типе Level и о связи с копией; ' + CL + '.' });
  add({ theorem: 'level_depth_eq', file: LN,
    claim: 'Там же лемма `level_depth_eq` связывает два столбца таблицы: `level_depth l = S (level_to_nat l)`.',
    note: 'level_depth_eq : forall l, level_depth l = S (level_to_nat l) (LevelNatIso.v:121). ' + CL + '.' });
  fix('Доказано: индуктивная структура «база плюс один конструктор следования» изоморфна стандартному `nat`; шаг `LSucc` переходит', 'level_nat_level', {
    claim: 'Доказано: индуктивная структура «база плюс один конструктор следования» изоморфна стандартному `nat`; шаг `LSucc` (на основном типе — `LS`) переходит при изоморфизме ровно в `S`.',
    note: 'Взаимная обратность — level_nat_level, nat_level_nat (в отдельном файле и в LevelNatIso.v); переход шага на основном типе — level_to_nat_LS (LevelNatIso.v:50). ' + CL + '.' });
  add({ theorem: 'every_hierarchy_is_the_level_series', file: LA,
    claim: 'Для «всякой» это доказано в общей форме (файл `LevelAscent.v`, теорема `every_hierarchy_is_the_level_series`): всякая структура «основание и надстраивание», в которой надстраивание инъективно, основание не есть результат надстраивания и действует индукция, нумеруется уровнями взаимно однозначно — основанию отвечает `L1`, надстраиванию — `LS`.',
    note: 'every_hierarchy_is_the_level_series : для всякого X с base, step при трёх посылках (step инъективен; base <> step x; индукция) — of_level L1 = base ' + AND + ' of_level (LS l) = step (of_level l) ' + AND + ' of_level инъективно ' + AND + ' сюръективно. ' + CL + '. Счёт с единицы — every_hierarchy_is_numbered_from_one.' });
  // --- § 3.5: блок восхождения (развилка — А)
  fix('Lemma level_has_successor : forall l : Level, exists l\', l\' = LS l.', 'level_has_successor', {
    theorem: 'LS_is_next_level', file: LA,
    claim: 'Theorem LS_is_next_level : forall l m : Level, l << m <-> (m = LS l ' + OR + ' LS l << m).',
    note: DONE + ' (развилка — А): блок заменён настоящими объявлениями. Прежняя первая лемма (exists l\', l\' = LS l) была верна для любой операции и в репозитории не объявлена. LS_is_next_level — ' + LA + ', § 3; ' + CL + '.' });
  fix('Lemma every_level_below_its_successor : forall l : Level, l << LS l.', 'every_level_below_its_successor', {
    theorem: 'level_lt_succ', file: TI,
    claim: 'Lemma level_lt_succ : forall L, L << LS L. Proof. intros L. simpl. left. reflexivity. Qed.',
    note: DONE + ' (развилка — А): имя приведено к исходнику. Lemma level_lt_succ (TransfiniteInductionLevel.v:61), текст доказательства совпадает дословно; ' + CL + '.' });
  fix('Обе доказываются немедленно из определений `LS` и ' + LL + '. Вместе они и означают', 'no_universal_level', {
    claim: 'Theorem no_universal_level : ~ exists Top : Level, forall L : Level, L << Top ' + OR + ' L = Top.',
    note: 'Формулировка блока совпадает с исходником (TransfiniteInductionLevel.v:83). ' + CL + '.' });
  add({ theorem: 'LS_is_next_level', file: LA,
    claim: 'Первая теорема — что он *ближайший* сверху: всякий уровень выше данного есть либо надстроенный над ним, либо лежит выше надстроенного.',
    note: 'Верно: LS_is_next_level : l << m <-> (m = LS l ' + OR + ' LS l << m); следствие — no_level_between : ~ (l << m ' + AND + ' m << LS l). ' + CL + '.' });
  add({ theorem: 'no_universal_level', file: TI,
    claim: 'Вторая — что уровня, под которым или в котором лежали бы все уровни, нет. Вместе они и означают: восхождение не упирается ни в какой высший уровень.[^5]',
    note: 'Верно: no_universal_level (TransfiniteInductionLevel.v:83); три утверждения блока сведены в ascent_has_no_top (' + LA + '). ' + CL + '.' });
  // --- § 3.7: перенос индукции
  const C_TR = 'Перенос проверен в обе стороны (файл `LevelAscent.v`): `level_induction_from_nat_ind` получает индукцию по уровням из `nat_ind`, `nat_induction_from_Level_ind` — индукцию по числам из `Level_ind`.';
  add({ theorem: 'level_induction_from_nat_ind', file: LA, claim: C_TR,
    note: 'level_induction_from_nat_ind : forall P : Level -> Prop, P L1 -> (forall l, P l -> P (LS l)) -> forall l, P l — доказана через nat_ind и взаимно обратные отображения LevelNatIso.v. ' + CL + '.' });
  add({ theorem: 'nat_induction_from_Level_ind', file: LA, claim: C_TR,
    note: 'nat_induction_from_Level_ind : forall P : nat -> Prop, P 0 -> (forall n, P n -> P (S n)) -> forall n, P n — доказана через Level_ind. ' + CL + '.' });
  add({ theorem: 'level_nat_level', file: LN,
    claim: 'Независимого вывода одной индукции из другой это не даёт: лемма о взаимной обратности отображений, на которую опирается перенос, сама доказана индукцией по уровню.',
    note: 'Верно: LevelNatIso.level_nat_level (:43) доказана тактикой induction l. Страница называет границу прямо.' });
  // --- § 3.8: разбор E/R/R
  fix('её формальная опора — индуктивный тип `Level` и доказанный изоморфизм с `nat`, причём строгий машинный изоморфизм установлен на', 'core_level_is_peano', {
    claim: 'её формальная опора — индуктивный тип `Level` и доказанный изоморфизм с `nat`: строгий машинный изоморфизм установлен и на *отдельной копии* типа уровней, и на самом Core-типе (§ 3.4).',
    note: DONE + ': было «установлен на отдельной копии». Об основном типе — core_level_is_peano (LevelNatIso.v:150); о копии — леммы L5_NatFromHierarchy.v. ' + CL + '.' });
  const C_R2 = 'Второе — *иррефлексивность* порядка (`hierarchy_irrefl`: ни один уровень не ниже самого себя) вместе с конечностью снизу: у иерархии есть основание, и ряд начинается с единицы (§ 3.3; теоремы `hierarchy_is_finite_from_below` и `level_depth_counts_from_one` файла `LevelAscent.v`).';
  fix('Второе — *иррефлексивность* порядка (`hierarchy_irrefl`: ни один уровень не ниже самого себя) вместе с конечностью снизу', 'hierarchy_irrefl', {
    claim: C_R2,
    note: 'hierarchy_irrefl : forall l, ~ level_lt l l (L5_NatFromHierarchy.v:84 — о копии; об основном типе — LevelNatIso.v:102 и level_lt_irrefl основного файла). Конечность снизу и счёт с единицы — названные теоремы LevelAscent.v. ' + CL + '.' });
  add({ theorem: 'hierarchy_is_finite_from_below', file: LA, claim: C_R2,
    note: 'hierarchy_is_finite_from_below : (forall l, ~ (l << L1)) ' + AND + ' (forall l, l = L1 ' + OR + ' L1 << l) ' + AND + ' (forall l, l = Nat.iter (pred (level_depth l)) LS L1) ' + AND + ' ~ (exists f : nat -> Level, forall n, f (S n) << f n). ' + CL + '.' });
  add({ theorem: 'level_depth_counts_from_one', file: LA, claim: C_R2,
    note: 'Счёт с единицы: level_depth L1 = 1 и взаимно однозначное соответствие уровней и положительных чисел. ' + CL + '.' });
  // --- сноски
  const C_FN1 = 'Из неё выведены фундированность порядка уровней (`level_lt_wf`) и несуществование бесконечно убывающей цепи (`no_infinite_level_regress`) — обе теоремы в файле `MetaPairStrength.v`, без аксиом.';
  fix('Из неё несуществование бесконечно убывающей цепи *выводимо*', 'level_lt_wf', {
    claim: C_FN1, page_price: 'без аксиом',
    note: DONE + ': сноска 1. Было «в репозитории пока не оформлено». level_lt_wf : well_founded level_lt (MetaPairStrength.v:128), из неё no_infinite_level_regress (:137). ' + CL + '.' });
  add({ theorem: 'no_infinite_level_regress', file: MP, claim: C_FN1, page_price: 'без аксиом',
    note: 'no_infinite_level_regress (MetaPairStrength.v:137). ' + CL + '.' });
  add({ theorem: 'hierarchy_is_finite_from_below', file: LA,
    claim: 'Конечность снизу одним утверждением — `hierarchy_is_finite_from_below` (файл `LevelAscent.v`): ниже основания уровней нет; всякий уровень есть основание либо лежит выше него; всякий уровень получен из основания конечным числом надстраиваний; бесконечно убывающей последовательности уровней нет.',
    note: 'Четыре конъюнкта теоремы названы на странице в том же порядке. ' + CL + '.' });
  const C_FN2 = 'Леммы `L1_minimal` и `level_lt_LS` файла `UniversePolymorphism.v`; файл подключает `TheoryOfSystems_Core_ERR.v` и говорит о его типе `Level`.';
  fix('В текущем `TheoryOfSystems_Core_ERR.v` этих двух лемм (`L1_minimal` и `level_lt_successor`) нет', 'L1_minimal', {
    claim: C_FN2,
    note: DONE + ': сноска 2. Было «нет как отдельных именованных утверждений… предмет будущей синхронизации». L1_minimal (UniversePolymorphism.v:225). ' + CL + '.' });
  fix('этих двух лемм (`L1_minimal` и `level_lt_successor`) нет как отдельных именованных утверждений', 'level_lt_successor', {
    theorem: 'level_lt_LS', file: UP, claim: C_FN2,
    note: DONE + ': сноска 2. Имени level_lt_successor в репозитории не было; лемма называется level_lt_LS (UniversePolymorphism.v:74). ' + CL + '.' });
  fix('Тип `Level`, как и функция глубины `level_depth` ниже, определён в файле `TheoryOfSystems_Core_ERR.v` Rocq-репозитория ToS; теоремы об отношении порядка', 'L5_hierarchy', {
    claim: 'леммы об отношении порядка уровней — там же; в файле `LawsFromDistinction.v` они повторены как теоремы о законе $L5$.',
    note: DONE + ': сноска 3. Леммы о порядке (level_lt_irrefl, level_lt_trans, level_lt_depth) доказаны в основном файле; L5_hierarchy, L5_transitivity, L5_no_infinite_descent (LawsFromDistinction.v) закрыты `exact` этими леммами.' });
  const C_FN5 = 'Лемма `level_lt_succ` и теорема `no_universal_level` — в файле `TransfiniteInductionLevel.v`; теорема `LS_is_next_level` — в файле `LevelAscent.v` (там же три утверждения сведены в одно: `ascent_has_no_top`).';
  fix('В текущем `TheoryOfSystems_Core_ERR.v` эти две леммы как отдельные именованные утверждения отсутствуют', 'level_lt_succ', {
    claim: C_FN5,
    note: DONE + ' (развилка — А): сноска 5. Файлы названы верно: level_lt_succ (:61) и no_universal_level (:83) — TransfiniteInductionLevel.v; LS_is_next_level — LevelAscent.v.' });
  add({ theorem: 'ascent_has_no_top', file: LA, claim: C_FN5,
    note: 'ascent_has_no_top : (forall l, l << LS l) ' + AND + ' (forall M, exists L, ~ (L << M ' + OR + ' L = M)) ' + AND + ' ~ (exists Top, forall L, L << Top ' + OR + ' L = Top). ' + CL + '.' });
  save();
}
