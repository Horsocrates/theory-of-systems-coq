// Часть I, шаг 4, страницы (2026-11-13, слово автора «Вноси»): 14 правок главы I.1 внесены; формализация —
// src/LevelForgetFunctor.v. Запуск: node patch-p01-step-04-pages.cjs  (затем relocate + merge по part01-ch01)
// Скрипт повторяем: приведённая запись пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть I, шаг 4, слово автора)';
const F = 'src/foundation/';
const CD = F + 'DistinctionCoDefinition.v';
const LF = 'src/LevelForgetFunctor.v';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0, dropped = 0;
  return {
    fix(prefix, th, fields, keepVerdict) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) &&
        (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
      if (hit.length === 0) return;
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix.slice(0, 50) + '» / ' + th + ', найдено ' + hit.length);
      Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
    },
    drop(prefix, th) {
      const before = j.records.length;
      j.records = j.records.filter((r) => !(norm(r.claim).startsWith(prefix) && r.theorem === th));
      dropped += before - j.records.length;
    },
    add(rec) {
      if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', снято ' + dropped + ', всего ' + j.records.length); },
  };
}
const a = open('part01-ch01.json');
const FORMULA = 'формула автора «вывод законов» оставлена; какого рода этот вывод (L2, L3 — поля записи; L4 — из поля exclusive; L1 — рефлексивность равенства; общий L3 — аксиома classic), теперь сказано на стр. 1188–1196 этой главы и в главе 3.';

// ---- место 6: inhabited
a.fix('В Rocq и в стандартной библиотеке `Coq.Logic.Inhabited` есть типовой класс', 'Inhabited', {
  theorem: 'inhabited', external: true,
  claim: 'В базовой библиотеке Rocq (модуль `Init.Logic`) есть индуктивный предикат, утверждающий, что некоторый тип *населён*, то есть имеет по крайней мере одного обитателя:',
  note: DONE + ': было «в стандартной библиотеке Coq.Logic.Inhabited есть типовой класс» — такого модуля и класса нет. Inductive inhabited (A : Type) : Prop := inhabits : A -> inhabited A (Corelib.Init.Logic).' });
a.fix('Class Inhabited (X : Type) : Prop := inhabited_witness : X.', null, {
  theorem: 'inhabits', external: true,
  claim: 'Inductive inhabited (A : Type) : Prop := inhabits : A -> inhabited A.',
  note: DONE + ': прежний блок (`Class Inhabited (X : Type) : Prop := inhabited_witness : X.`) компилятор не принимал (Universe inconsistency). Нынешний блок — объявление базовой библиотеки.' });
a.drop('(Точное определение в стандартной библиотеке немного отличается, используя `inhabits`', 'inhabits');
a.add({ theorem: 'Logic', external: true,
  claim: 'В базовой библиотеке Rocq (модуль `Init.Logic`) есть индуктивный предикат',
  note: 'Имя модуля базовой библиотеки (Corelib.Init.Logic), не объявление формализации.' });

// ---- место 3
const P3 = DONE + ': фразы автора сохранены; следом добавлено, что в формализации связь проведена порядком изложения, а не зависимостью файлов (от Distinction.v зависит цепочка основания; ядро, процессы и категории его не подключают).';
a.fix('В математической работе тома акт различения играет роль *первого формализуемого*', null, { note: P3 });
a.fix('акт различения находится в основании дедуктивной цепи, и каждый последующий объект тома', null, { note: P3 });
a.add({ theorem: null,
  claim: 'В самой формализации эта связь проведена порядком изложения, а не зависимостью файлов: от записи `Distinction` формально зависит цепочка основания — законы, принципы, E/R/R, — тогда как числа, процессы и категории систем определены на индуктивных типах Rocq и файла записи не подключают.',
  note: 'Граф зависимостей (coqdep): от foundation/Distinction.v прямо или через другие файлы зависят файлы каталогов foundation и stdlib; TheoryOfSystems_Core_ERR.v, ToS_Axioms.v, CauchyReal.v, process/ProcessCore.v, SystemCategory.v, LevelFunctors.v в их числе нет.' });
a.fix('Дальнейшая работа тома получает прочный фундамент в виде формального объекта', null, {
  note: 'закрыто 13.11 (Часть I, шаг 4): фраза автора не менялась; что зависит от записи формально, сказано на стр. 1101–1106.' });

// ---- место 2
a.fix('В репозитории `theory-of-systems-coq` запись `Distinction` исторически появилась раньше', 'Distinction', {
  claim: 'В репозитории `theory-of-systems-coq` запись `Distinction` стоит в файле `foundation/Distinction.v`, с которого начинается цепочка основания: от неё идут теоремы о законах, принципах и E/R/R.',
  note: DONE + ': было «исторически появилась раньше других основных структур и служит основанием для дальнейших определений». Цепочка: Distinction.v → LawsFromDistinction.v → PrinciplesFromLaws.v → PrinciplesToERR.v, ERRFromDistinction.v.' });
a.add({ theorem: null,
  claim: 'По времени записи она не первая: файл внесён в марте 2026 года, после определений уровней, систем и процессов.',
  note: 'История репозитория: foundation/Distinction.v — коммит 36ef3ff, 19.03.2026; Level, System (TheoryOfSystems_Core_ERR.v), RealProcess — коммит 06db789, 19.01.2026; process/ProcessCore.v — 14.03.2026.' });
a.fix('Это — технический факт о порядке файлов и теорем в репозитории, не претендующий', null, {
  note: DONE + ': сама фраза не менялась; факт, к которому она относится, теперь назван по истории репозитория.' });
a.fix('Все три смысла «первого» — онтологический (порождает время), структурный', null, {
  claim: 'Три смысла «первого» — онтологический (порождает время), структурный (базовый для дедукции), технический (начало цепочки основания в репозитории) — имеют разные основания и работают на разных уровнях.',
  note: DONE + ': было «согласованы между собой… совпадают на одном объекте»; технический смысл теперь — начало цепочки основания, а не приоритет в репозитории.' });

// ---- место 1
a.fix('Но в Главе 3 акт различения станет основанием для *вывода* законов логики', null, { note: 'закрыто 13.11 (Часть I, шаг 4): ' + FORMULA });
a.fix('что он формализуем в CIC; что он минимален; что из него выводимы дальнейшие структуры', null, { note: 'закрыто 13.11 (Часть I, шаг 4): ' + FORMULA });
const OLD1188 = 'В Главе 3 будет показано, что из структуры `Distinction` *выводятся* законы логики $L1, L2, L3, L4$ как теоремы Rocq о свойствах этой записи.';
const NEW1188 = 'В Главе 3 будет показано, что из структуры `Distinction` *выводятся* законы логики $L1, L2, L3, L4$ как теоремы Rocq о свойствах этой записи, — и какого рода этот вывод: $L2$ и $L3$ для сторон записи даны её полями `exclusive` и `exhaustive`, $L4$ получается из поля `exclusive` одним шагом, $L1$ есть рефлексивность равенства.';
for (const th of ['L1_stability', 'L2_exclusivity', 'L3_totality', 'L4_self_grounding'])
  a.fix(OLD1188, th, { claim: NEW1188, note: DONE + ': к формуле автора добавлено, какого рода вывод. ' + th + ' — Closed under the global context.' });
a.add({ theorem: 'every_prop_distinguishes_iff_EM', file: CD, page_price: 'без аксиом',
  claim: 'Исключённое третье для произвольной пропозиции из записи не выводится: оно принято аксиомой `classic`, и доказано без аксиом, что оно равносильно тому, что всякая пропозиция есть положительная сторона некоторого различения (`every_prop_distinguishes_iff_EM`).',
  note: 'every_prop_distinguishes_iff_EM : (forall P, exists D, positive D = P) <-> (forall P, P \\/ ~ P). Closed under the global context.' });
a.fix('Из него выводятся законы логики (Глава 3), типизация (Глава 2.4), онтология', null, {
  claim: 'Из него выводятся законы логики (Глава 3), типизация (Глава 2.4), онтология положительно-отрицательного (Глава 5).',
  note: DONE + ': номер главы о со-определении исправлен (было «Глава 4»). ' + FORMULA });

// ---- место 5
const OLD1204 = 'В последующей главе об аксиоматическом слое Rocq будут проговорены технические аксиомы, на которые опирается работа с `Distinction`';
const NEW1204 = 'В последующей главе об аксиоматическом слое Rocq будут проговорены технические аксиомы формализации — `classic`, на которую опирается работа с `Distinction`, и `L4_witness`, которая нужна дальше, при извлечении свидетеля';
a.fix(OLD1204, 'classic', { claim: NEW1204 }, true);
a.fix(OLD1204, 'L4_witness', { claim: NEW1204, page_price: 'аксиома формализации; работа с Distinction на неё не опирается',
  note: DONE + ': было «аксиомы, на которые опирается работа с Distinction (classic и L4_witness)». Ни одна теорема о записи Distinction от L4_witness не зависит.' });

// ---- место 4
const OLD1253 = 'Первое формализуемое по эту сторону границы — сама схема перехода между уровнями (функторы `forget` и `embed` с их сопряжением).';
const NEW1253 = 'Первое формализуемое по эту сторону границы — сама схема перехода между уровнями (функторы забывания и вложения — `ForgetFunctor` и `EmbedToForgettable` — с их сопряжением `LevelAdj` на забываемых системах).';
a.fix(OLD1253, 'forget', { theorem: 'ForgetFunctor', file: LF, claim: NEW1253,
  note: DONE + ': было `forget` — такого имени нет. ForgetFunctor (L : Level) : Functor (ForgettableCat L) (SystemCat L) — забывание как функтор на полной подкатегории забываемых систем. Closed under the global context.' });
a.fix(OLD1253, 'embed', { theorem: 'EmbedToForgettable', file: LF, claim: NEW1253,
  note: DONE + ': было `embed` — под этим именем в формализации другие объекты. EmbedToForgettable (L : Level) : Functor (SystemCat L) (ForgettableCat L). Closed under the global context.' });
a.fix(OLD1253, 'level_adjunction', { theorem: 'LevelAdj', file: LF, claim: NEW1253,
  note: DONE + ': LevelAdj (L : Level) : Adjunction (SystemCat L) (ForgettableCat L) — вложение слева, забывание справа; оба тождества треугольника — level_adj_is_adjunction. Closed under the global context.' });
a.add({ theorem: 'level_adj_is_adjunction', file: LF, claim: NEW1253,
  note: 'level_adj_is_adjunction : forall L, is_adjunction (LevelAdj L). Closed under the global context. Естественность единицы и коединицы: level_adj_unit_natural, level_adj_counit_natural; взаимно обратные отображения морфизмов: embed_forget_hom_bijection. Сужение на забываемые системы вынуждено: no_functor_to_base, forgettable_subcategory_is_proper.' });
a.save();
