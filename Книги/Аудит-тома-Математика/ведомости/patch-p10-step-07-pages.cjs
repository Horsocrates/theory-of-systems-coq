// Часть X, шаг 7, страницы (2026-11-13, слово автора «А, продолжай»): восемь мест главы X.6 и одно место
// главы IV.1 внесены; прежний классический путь леммы Диксона снят из HigmanLemma.v (вариант А).
// Запуск: node patch-p10-step-07-pages.cjs   (затем relocate + merge по part10-ch06 и part04-ch01)
// Скрипт повторяем: запись, уже приведённая к новым словам, пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть X, шаг 7, слово автора)';
const S = 'src/settheory/';
const FG = 'src/foundation/FiniteGameDeterminacy.v';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0, dropped = 0;
  return {
    fix(prefix, th, fields, keepVerdict) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || r.theorem === th));
      if (hit.length === 0) return;
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix.slice(0, 50) + '» / ' + th + ', найдено ' + hit.length);
      Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
    },
    reclaim(prefix, claim) { for (const r of j.records) if (norm(r.claim).startsWith(prefix)) { r.claim = claim; n++; } },
    drop(prefix, th) {
      const before = j.records.length;
      j.records = j.records.filter((r) => !(norm(r.claim).startsWith(prefix) && r.theorem === th));
      dropped += before - j.records.length;
    },
    add(rec) {
      if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', снято ' + dropped + ', всего ' + j.records.length); },
  };
}
const TREE = 'finite_game_strategically_determined : forall g, (Win g \\/ Lose g) /\\ ~ (Win g /\\ Lose g) /\\ (mover_wins g = true <-> Win g) /\\ (mover_wins g = false <-> Lose g). Closed under the global context.';
const ZER = 'zermelo_determinacy (settheory/ZermeloDeterminacy.v) : forall W K, determined W K — стратегия есть у одного из двух игроков; Axioms: BorelDeterminacy.classic, ToS_Axioms.L4_witness.';
const DICK = 'dickson_pair доказана конструктивно (dickson_pair_constructive); higman_synthesis, wqo_nat_pair — Closed under the global context. Прежний классический путь (right_min, tail_min_exists, right_min_unbounded) снят по слову автора (вариант А); в файле 16 Qed и ни одного допущения.';

const a = open('part10-ch06.json');
// ---- основной текст
a.fix('*Лемма Хигмана*: списки над конечным алфавитом образуют хорошо-квазиупорядочение (wqo) — доказано для', 'higman_unit', { page_price: '',
  claim: '*Лемма Хигмана*: списки над конечным алфавитом образуют хорошо-квазиупорядочение (wqo) — доказан случай однобуквенного алфавита (он сводится к wqo на длинах); рядом доказаны wqo для самих $\\mathtt{bool}$ и $ℕ$ и лемма Диксона для пар.[^1]',
  note: DONE + ': было «доказано для конкретных алфавитов (единичного, булева, ℕ) с леммой Диксона в основе». higman_unit : is_wqo (list_le (fun _ _ : unit => True)); wqo_bool, wqo_nat_le — о самих bool и nat. Closed under the global context. Алфавит из двух и более букв не доказан — горизонт.' });
a.reclaim('*Теорема Крускала*: конечные деревья wqo под гомеоморфным вложением — доказано для конкретных семейств (цепи, вилки, растущие',
  '*Теорема Крускала*: конечные деревья wqo под гомеоморфным вложением — доказано для конкретных семейств (цепи, вилки, деревья глубины $\\le 1$).[^2]');
a.fix('*Кантор–Бендиксон*: производная замкнутого множества как процесс, $\\omega$-предел — совершенное ядро.', undefined, { theorem: 'stable_stage_is_perfect_kernel', file: S + 'CantorBendixsonFull.v',
  claim: '*Кантор–Бендиксон*: производная множества как процесс; $\\omega$-предел итераций содержит всякое совершенное подмножество, а при стабилизации на конечном шаге совпадает с совершенным ядром.[^3]',
  note: DONE + ': было «ω-предел — совершенное ядро» — теоремы не было, и в общем виде она неверна. perfect_kernel_in_omega : subset P A -> is_perfect P -> subset P (CB_omega A); stable_stage_is_perfect_kernel: при стабилизации на шаге n этот шаг совершенен, равен ω-пределу и содержит всякое совершенное подмножество. Closed under the global context.' });
a.fix('И *конечная детерминированность игр* (Цермело, 1913): всякая конечная игра определена.', 'weak_determinacy', { theorem: 'zermelo_determinacy', file: S + 'ZermeloDeterminacy.v', page_price: '',
  claim: 'И *конечная детерминированность игр* (Цермело, 1913): в игре конечной длины выигрышная стратегия есть у одного из игроков.[^4]',
  note: DONE + ': прежде для произвольной игры было доказано только «у первого игрока стратегия либо есть, либо её нет» (weak_determinacy). ' + ZER });
a.fix('ToS проводит их *конструктивные ядра для конкретных семейств* без выбора — но *не* в полной общности.', undefined, { page_price: 'без выбора',
  note: DONE + ': слова прежние, за ними добавлена оговорка об играх с бесконечным числом ходов. ' + DICK + ' Крускал (семейства), Кантор — Бендиксон, деревья игры — Closed. ' + ZER });
a.fix('Без выбора доказуемы и wqo-результаты (Хигман, Крускал — для конкретных семейств) и конечная', undefined, { theorem: 'finite_game_strategically_determined', file: FG,
  claim: 'Без выбора доказуемы wqo-результаты (Хигман — для однобуквенного алфавита, Крускал — для конкретных семейств) и детерминированность конечных деревьев игры; для игр конечной длины с бесконечным числом ходов стратегию приходится извлекать — ценой L3 и L4.',
  note: DONE + ': было «…и конечная (цермеловская) детерминированность». ' + TREE + ' ' + ZER });
a.fix('Это конструктивные ядра «высоких» теорем, не их полная общность.', undefined, {
  claim: 'Это ядра «высоких» теорем, не их полная общность.*',
  note: DONE + ': слово «конструктивные» снято: детерминированность игр конечной длины стоит на classic и L4_witness. Остальные ядра — Closed under the global context.' });
a.fix('конечная детерминированность — обратная индукция на дереве игры, тоже без башни', 'finite_game_determined', { theorem: 'finite_game_strategically_determined', file: FG, page_price: '0 аксиом',
  note: DONE + ': страница не менялась; слова теперь опираются на теорему, связывающую обратную индукцию с выигрышем. ' + TREE + ' Прежняя finite_game_determined утверждала лишь, что булево значение равно true или false.' });
a.fix('для конкретных семейств, конечная детерминированность.', 'zero_game_determined', { theorem: 'finite_game_strategically_determined', file: FG,
  note: DONE + ': страница не менялась. ' + TREE + ' ' + ZER });
// ---- сноска 1
const F1OLD = '`HigmanLemma.v`: `is_wqo`, `wqo_nat_le`, `dickson_pair`, `higman_unit`';
const F1NEW = '`HigmanLemma.v`: `is_wqo`, `wqo_nat_le`, `higman_unit` (списки над однобуквенным алфавитом), `dickson_pair` (лемма Диксона для пар, доказана конструктивно), `wqo_nat_pair`, итог — `higman_synthesis`.';
a.fix(F1OLD, 'dickson_pair', { claim: F1NEW, page_price: '0 аксиом', note: DONE + '. ' + DICK }, true);
a.fix(F1OLD, 'higman_synthesis', { claim: F1NEW, page_price: '0 аксиом', note: DONE + '. ' + DICK }, true);
a.reclaim(F1OLD, F1NEW);
a.fix('15 Qed, использует `classic` (L3).', undefined, { claim: '16 Qed, 0 аксиом.', page_price: '0 аксиом', note: DONE + ': было «15 Qed, использует classic (L3)». ' + DICK });
// ---- сноска 2
const F2OLD = '`KruskalFull.v`/`KruskalTree.v`: `chain_wqo`, `fork_wqo`, `growing_wqo`';
const F2NEW = '`KruskalTree.v`: `kruskal_chains`, `kruskal_forks` — любая последовательность цепей, любая последовательность вилок; `KruskalFull.v`: `depth1_wqo` (звёзды), `depth_le1_wqo` (деревья глубины $\\le 1$, листья и звёзды вперемешку).';
a.fix(F2OLD, 'chain_wqo', { claim: F2NEW, theorem: 'kruskal_chains', file: S + 'KruskalTree.v', page_price: '0 аксиом',
  note: DONE + ': было имя chain_wqo — лемма об одной фиксированной последовательности. kruskal_chains : is_wqo (fun m n => tree_embed (chain m) (chain n)) — любая последовательность цепей. Closed under the global context.' });
a.fix(F2OLD, 'fork_wqo', { claim: F2NEW, theorem: 'kruskal_forks', file: S + 'KruskalTree.v', page_price: '0 аксиом',
  note: DONE + ': было имя fork_wqo — лемма об одной фиксированной последовательности. kruskal_forks — любая последовательность вилок. Closed under the global context.' });
a.fix(F2OLD, 'growing_wqo', { claim: F2NEW, theorem: 'depth_le1_wqo', file: S + 'KruskalFull.v', page_price: '0 аксиом',
  note: DONE + ': было имя growing_wqo — лемма, возвращающая свою посылку. depth_le1_wqo : (forall k, depth_le1 (f k)) -> exists i j, i < j /\\ tree_embed (f i) (f j) — любая последовательность деревьев глубины <= 1. Closed under the global context.' });
a.drop(F2OLD, 'L5_from_kruskal');
a.reclaim(F2OLD, F2NEW);
a.fix('15 Qed, 0 новых аксиом.', undefined, { claim: '19 и 12 Qed, 0 аксиом.', note: DONE + ': было «15 Qed»; в KruskalTree.v 19 Qed, в KruskalFull.v 12.' });
// ---- сноска 3
a.reclaim('`CantorBendixsonFull.v`: `CB_deriv` (удаление изолированных точек)', '`CantorBendixsonFull.v`: `CB_deriv` (точки накопления), `CB_iter`, `CB_omega` ($\\omega$-предел).');
a.fix('совершенное-или-пустое ядро', undefined, { theorem: 'perfect_kernel_in_omega', file: S + 'CantorBendixsonFull.v', page_price: '0 аксиом',
  claim: 'Всякое совершенное подмножество лежит в $\\omega$-пределе (`perfect_kernel_in_omega`); при стабилизации на конечном шаге этот шаг совершенен и совпадает с $\\omega$-пределом (`stable_stage_is_perfect_kernel`);',
  note: DONE + ': было «совершенное-или-пустое ядро» — такой теоремы в файле не было. Closed under the global context.' });
a.fix('конечные множества рассеяны', 'S_finite_scattered', { theorem: 'finite_set_scattered', file: S + 'CantorBendixsonFull.v', page_price: '0 аксиом',
  claim: 'всякое конечное множество рассеяно (`finite_set_scattered`).',
  note: DONE + ': прежде доказано было для одного множества {0, 1, 2} (S_finite_scattered). finite_set_scattered : forall l : list Q, is_scattered (in_list l). Closed under the global context.' });
a.fix('20 Qed, 0 аксиом.', undefined, { claim: '35 Qed, 0 аксиом.', note: DONE + ': было 20; в CantorBendixsonFull.v 35 Qed.' });
// ---- сноска 4
const F4OLD = '`BorelDeterminacy.v`: `weak_determinacy`, `zero_game_determined`.';
const F4NEW = '`BorelDeterminacy.v`: `weak_determinacy` — исключённое третье для «у первого игрока есть стратегия», и частные случаи (`zero_game_determined`);';
a.fix(F4OLD, 'weak_determinacy', { claim: F4NEW, page_price: 'classic',
  note: DONE + ': weak_determinacy : forall W K, determined_weak W K — вид «P или не P»; Axioms: BorelDeterminacy.classic. Страница это теперь говорит.' });
a.reclaim(F4OLD, F4NEW);
a.fix('15 Qed, 1 аксиома (`classic`).', undefined, { claim: '19 Qed, 1 аксиома (`classic`).', verdict: 'ok', note: DONE + ': было 15; в BorelDeterminacy.v 19 Qed.' });
a.fix('NB: вопреки имени файла, доказана именно *конечная* (цермеловская) детерминированность', undefined, { theorem: 'zermelo_determinacy', file: S + 'ZermeloDeterminacy.v',
  claim: 'NB: вопреки имени файла `BorelDeterminacy.v`, борелевская (Мартина) детерминированность здесь не доказана.',
  note: DONE + '. ' + ZER });
// ---- сноска 7
a.fix('`foundation/FiniteGameDeterminacy.v` (`finite_game_determined`, обратная индукция)', 'finite_game_determined', { theorem: 'finite_game_strategically_determined', file: FG, page_price: '0 аксиом',
  claim: '`foundation/FiniteGameDeterminacy.v` (`finite_game_strategically_determined`: каждая позиция конечного дерева выиграна ровно одной стороной, и обратная индукция `mover_wins` вычисляет, какой)',
  note: DONE + '. ' + TREE });
// ---- новые записи
a.add({ theorem: 'zermelo_determinacy', file: S + 'ZermeloDeterminacy.v', page_price: 'classic и L4_witness',
  claim: '`ZermeloDeterminacy.v`: `zermelo_determinacy` — при любом условии выигрыша и любом числе раундов стратегия есть у одного из игроков; цена — `classic` и `L4_witness` (ходов бесконечно много, стратегию приходится извлекать).',
  note: 'Новый файл шага 7. ' + ZER });
a.add({ theorem: 'finite_game_strategically_determined', file: FG, page_price: 'без допущений',
  claim: 'Для конечных деревьев игры — без допущений: `finite_game_strategically_determined` (`foundation/FiniteGameDeterminacy.v`).',
  note: TREE });
a.add({ theorem: 'zermelo_determinacy', file: S + 'ZermeloDeterminacy.v', page_price: 'L3 и L4 в полную силу',
  claim: 'Одна оговорка: детерминированность игр с бесконечным числом ходов на каждом шаге требует извлечь стратегию и потому стоит на L3 и L4, взятом в полную силу; для конечных деревьев игры она доказана без допущений.',
  note: ZER + ' ' + TREE });
a.add({ theorem: 'wqo_nat_pair', file: S + 'HigmanLemma.v', page_price: '0 аксиом', claim: F1NEW,
  note: 'wqo_nat_pair : is_wqo (fun p q : nat * nat => fst p <= fst q /\\ snd p <= snd q). Closed under the global context.' });
a.add({ theorem: 'CB_ord', file: S + 'CantorBendixsonFull.v', page_price: '',
  claim: 'В общем случае $\\omega$-предел совершенным ядром не является: ядро достигается продолжением итерации вдоль нотаций (`CB_ord`).',
  note: 'Fixpoint CB_ord — итерация производной вдоль Ord (шаг 6). Что ω-предел в общем случае не совершенен — известный факт (множество ранга ω + 1); примера в формализации нет, теорема об этом не доказана.' });
a.save();

const c = open('part04-ch01.json');
c.fix('Все утверждения файла верны для любой такой таблицы и допущений не имеют.', undefined, { page_price: 'одна лемма на classic',
  claim: 'Все утверждения файла верны для любой такой таблицы; допущений они не имеют, кроме одной леммы на исключённом третьем (`pi11_negation`).',
  note: DONE + ': поправка неточности шага 6 («допущений не имеют»). pi11_negation — Axioms: Classical_Prop.classic; остальные утверждения файла — Closed under the global context.' });
c.save();
