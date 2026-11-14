// Часть II, шаг 2, страницы (2026-11-13, слово автора «Вноси»): 12 правок главы II.1 (асимметрия, роль-сторона,
// пары порядков, process_equiv, девятки) и 2 правки главы II.2 (имя свидетеля в § 2.4) внесены.
// Формализация — новые файлы src/foundation/DistinctionSideRole.v и src/process/ProcessEquivLimit.v; правки в
// AsymmetricDistinction.v (доказательство distinction_asymmetric без classic; swap_changes_positive_of_any),
// PrimalityOfOne.v (пары порядков), CountingPresence.v (conceptual_ordering_from_counts).
// Запуск: node patch-p02-step-02-pages.cjs  (затем relocate + merge по part02-ch01 и part02-ch02). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть II, шаг 2, слово автора)';
const F = 'src/foundation/';
const P = 'src/process/';
const CP = F + 'CountingPresence.v';
const SR = F + 'DistinctionSideRole.v';
const AD = F + 'AsymmetricDistinction.v';
const PO = F + 'PrimalityOfOne.v';
const EL = P + 'ProcessEquivLimit.v';
const NP = P + 'ProcessNinePoint.v';
const CL = 'Closed under the global context';
const BS = String.fromCharCode(92);
const NEG = BS + 'neg';
const MAPSTO = BS + 'mapsto';
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

// ---------------------------------------------------------------- II.1
{
  const { fix, add, save } = open('part02-ch01');

  // --- блок роли-стороны и сноска 3
  const C_ROLE = 'Точнее это последнее утверждение формализуется не через доказательства, а через *роль-сторону* — так (файл `DistinctionSideRole.v`; тип сторон `Side := Marked | Unmarked` взят из `Binarity.v`):';
  fix('Точнее это последнее утверждение формализуется не через доказательства, а через *роль-сторону* — например, так:', 'marked_role_gt_unmarked_role', {
    file: SR, claim: C_ROLE,
    note: DONE + ' (формализацией): блок, который страница предлагала, внесён — ' + SR + '. marked_role_gt_unmarked_role : side_value Unmarked < side_value Marked. ' + CL + '. Первая строка блока стала Definition DistinctionSide : Set := Side (тип сторон уже был в Binarity.v:11).' });
  add({ theorem: 'Side', file: F + 'Binarity.v', claim: C_ROLE,
    note: 'Inductive Side := Marked | Unmarked (Binarity.v:11); DistinctionSide определён через него.' });
  const C_FN3 = 'Это усиление внесено: `DistinctionSide`, `side_value` и теорема `marked_role_gt_unmarked_role` — в файле `DistinctionSideRole.v` (тип сторон `Side` взят из `Binarity.v`).';
  fix('Тип `DistinctionSide` и `side_value` в текущем репозитории отсутствуют', 'DistinctionSide', {
    file: SR, claim: C_FN3,
    note: DONE + ' (формализацией): сноска 3. Definition DistinctionSide : Set := Side (' + SR + ').' });
  fix('`side_value` в текущем репозитории отсутствуют', 'side_value', {
    file: SR, claim: C_FN3,
    note: DONE + ' (формализацией): сноска 3. side_value (s : DistinctionSide) : nat := match s with Marked => 1 | Unmarked => 0 end.' });
  const C_MARK = 'Там же доказано, что `mark` и `unmark` возвращают именно эти значения ролей (`mark_is_marked_value`, `unmark_is_unmarked_value`)';
  fix('До его внесения формальным носителем приоритета остаётся пара `mark` / `unmark`', 'mark', {
    claim: C_MARK,
    note: DONE + ': сноска 3. mark, unmark (AsymmetricDistinction.v) — константы 1 и 0; их связь с ролями теперь теорема.' });
  add({ theorem: 'mark_is_marked_value', file: SR, claim: C_MARK,
    note: 'mark_is_marked_value : forall (D : Distinction) (p : positive D), mark D p = side_value Marked. ' + CL + '.' });
  add({ theorem: 'unmark_is_unmarked_value', file: SR, claim: C_MARK,
    note: 'unmark_is_unmarked_value : forall (D : Distinction) (n : negative D), unmark D n = side_value Unmarked. ' + CL + '.' });
  add({ theorem: 'exactly_one_side_holds', file: SR,
    claim: 'что из двух ролей всякого различения выполнена ровно одна (`exactly_one_side_holds`)',
    note: 'exactly_one_side_holds : forall D, exists s, side_holds D s /' + BS + ' (forall s\', side_holds D s\' -> s\' = s). Существование — из exhaustive, единственность — из exclusive. ' + CL + '.' });
  add({ theorem: 'distinction_order_from_roles', file: SR,
    claim: 'и что пара `distinction_order` есть пара значений двух ролей (`distinction_order_from_roles`).',
    note: 'distinction_order_from_roles : distinction_order = (side_value Marked, side_value Unmarked). ' + CL + '.' });
  add({ theorem: 'side_value', file: SR,
    claim: 'Само сопоставление «маркированной — $1$, немаркированной — $0$» остаётся определением — записью прочтения, а не выводом.',
    note: 'Верно: side_value — определение (match), значения вписаны рукой; страница называет статус прямо.' });

  // --- асимметрия: блок и сноска 4
  fix('Proof. (* ... uses classic ... *) Qed.', 'distinction_asymmetric', {
    claim: 'Proof. (* ... *) Qed.',
    note: DONE + ': пометка «uses classic» снята. Доказательство заменено при той же формулировке (13.11); Print Assumptions distinction_asymmetric — ' + CL + '.' });
  fix('Это уместно: утверждение «$P$ и $' + NEG + ' P$ не совпадают» есть утверждение об *определённости* различия', 'distinction_asymmetric', {
    claim: 'Утверждение `distinction_asymmetric` — «$P$ и $' + NEG + ' P$ не совпадают» — доказано без допущений',
    page_price: 'без допущений',
    note: DONE + ' (формализацией): сноска 4. Было: цена classic названа «формальным следом закона». Теперь утверждение доказано без аксиомы; ' + CL + '.' });
  fix('Доказательство `distinction_asymmetric` опирается на аксиому `classic`', 'classic', {
    claim: '(до 13.11.2026 доказательство шло через аксиому `classic`, но утверждению она не нужна)',
    note: DONE + ': сноска 4. Верно: прежнее доказательство содержало destruct (classic P); нынешнее аксиому не применяет.' });
  const C_GEN = 'В общей форме — для всякого различения, а не только канонического — то же дают `swap_changes_positive_of_any` (тот же файл) и `sides_distinct` (файл `DistinctionCoDefinition.v`)';
  add({ theorem: 'swap_changes_positive_of_any', file: AD, claim: C_GEN,
    note: 'swap_changes_positive_of_any : forall D : Distinction, positive D <> positive (swap_distinction D). ' + CL + '.' });
  add({ theorem: 'sides_distinct', file: F + 'DistinctionCoDefinition.v', claim: C_GEN,
    note: 'sides_distinct : forall D : Distinction, positive D <> negative D (DistinctionCoDefinition.v:125). ' + CL + '.' });
  add({ theorem: 'sides_distinct', file: F + 'DistinctionCoDefinition.v',
    claim: 'различность сторон следует из двух правил записи, несовместности ($L2$) и исчерпанности ($L3$ для сторон). Закон $L3$ участвует здесь как правило самой записи, а не как аксиома `classic`.',
    note: 'Верно: доказательство применяет поля exclusive и exhaustive записи Distinction; аксиома classic в терм не входит (' + CL + ').' });

  // --- пары порядков: § 1.4.2, сноска 5, § 1.4.3
  fix('В репозитории оба порядка присутствуют явно, и их различённость зафиксирована формально. Файл', 'distinction_order', {
    theorem: 'orderings_dual_pairs', file: PO,
    claim: 'В репозитории оба порядка присутствуют явно, и их различённость зафиксирована формально (теорема `orderings_dual_pairs`, см. ниже).',
    note: DONE + ' (формализацией): было «зафиксирована формально» при одной паре (1,0). orderings_dual_pairs : fst tos_conceptual_ordering = snd number_ordering /' + BS + ' snd tos_conceptual_ordering = fst number_ordering /' + BS + ' tos_conceptual_ordering <> number_ordering. ' + CL + '.' });
  const C_PAIRS = '*Формальная* запись двойственности двух порядков как пары $(1,0)$ против пары $(0,1)$ дана в том же файле отдельно: пары `tos_conceptual_ordering` $:= (1,0)$ и `number_ordering` $:= (0,1)$ и теорема `orderings_dual_pairs` — пары зеркальны и различны;';
  fix('Поэтому *формальная* запись двойственности двух порядков как пары $(1,0)$ против пары $(0,1)$ содержится именно в', 'distinction_order', {
    theorem: 'orderings_dual_pairs', file: PO, claim: C_PAIRS,
    note: DONE + ' (формализацией): было «содержится именно в AsymmetricDistinction.v» — там одна пара. Теперь обе пары и теорема о них — в PrimalityOfOne.v (то, что предлагала сноска 5).' });
  add({ theorem: 'tos_conceptual_ordering', file: PO, claim: C_PAIRS,
    note: 'Definition tos_conceptual_ordering : nat * nat := (1%nat, 0%nat). Пара вписана рукой.' });
  add({ theorem: 'number_ordering', file: PO, claim: C_PAIRS,
    note: 'Definition number_ordering : nat * nat := (0%nat, 1%nat). Пара вписана рукой; number_ordering_is_numerical : fst < snd.' });
  add({ theorem: 'distinction_order_is_conceptual', file: PO,
    claim: 'пара `distinction_order` из `AsymmetricDistinction.v` есть первая из них (`distinction_order_is_conceptual`).',
    note: 'distinction_order_is_conceptual : distinction_order = tos_conceptual_ordering. ' + CL + '.' });
  fix('`PrimalityOfOne.v` регистрирует ту же мысль в более слабой форме', 'tos_first', {
    claim: 'Имена `tos_first` и `tos_absence` регистрируют ту же мысль в более слабой форме: числовой порядок $0 < 1$ налицо, и онтологическое имя начала (`tos_first`) сопоставлено единице, а не нулю.[^5]',
    note: 'Definition tos_first := 1%nat; tos_absence := 0%nat (PrimalityOfOne.v) — имена чисел; numerical_ordering : (0 < 1)%nat. Статус («регистрируют», «в более слабой форме») назван честно.' });
  fix('`tos_ordering`, задающее порядок обоснования.', 'tos_ordering', {
    claim: '`tos_ordering`, сохраняющее при этом чтении числовой порядок $0 < 1$;',
    note: DONE + ': было «задающее порядок обоснования». tos_ordering : (tos_absence < tos_first)%nat — после раскрытия 0 < 1, числовой порядок.' });
  add({ theorem: 'tos_conceptual_ordering', file: PO,
    claim: 'пара `tos_conceptual_ordering`, записывающая порядок обоснования.',
    note: 'Пара (1, 0), вписанная рукой: запись порядка обоснования, а не его вывод (сноска 5 страницы говорит это прямо).' });
  // сноска 5
  fix('До такой синхронизации том опирается на `distinction_order` как на формальный носитель пары', 'distinction_order', {
    theorem: 'tos_conceptual_ordering', file: PO,
    claim: 'Эта синхронизация внесена 13.11.2026: пары `tos_conceptual_ordering` $:= (1,0)$ и `number_ordering` $:= (0,1)$ и теорема `orderings_dual_pairs` — в `PrimalityOfOne.v`;',
    note: DONE + ' (формализацией): сноска 5. Определения и теорема добавлены в PrimalityOfOne.v после orderings_dual.' });
  fix('Чтобы `orderings_dual` в `PrimalityOfOne.v` фиксировала именно две противоположные пары', 'orderings_dual', {
    claim: '`orderings_dual` оставлена как есть.',
    note: DONE + ': сноска 5. orderings_dual : (tos_absence < tos_first)%nat /' + BS + ' (0 < 1)%nat — не менялась; ' + CL + '.' });
  fix('как уже сделано для `distinction_order` в `AsymmetricDistinction.v`.', 'distinction_order', {
    theorem: 'orderings_dual_pairs', file: PO,
    claim: 'Обе пары вписаны рукой: теорема говорит об этих двух записях — что они зеркальны и различны, — а не выводит порядок обоснования.',
    note: DONE + ': сноска 5. Верно: обе пары — определения; orderings_dual_pairs сравнивает две записи. Порядок обоснования как теорема не получен — страница говорит это прямо.' });
  add({ theorem: 'conceptual_ordering_from_counts', file: CP,
    claim: 'Что считают компоненты пары $(1,0)$, сказано теоремой `conceptual_ordering_from_counts` (файл `CountingPresence.v`): первая — счёт одного совершённого акта, вторая — счёт пустого списка.',
    note: 'conceptual_ordering_from_counts : forall D : Distinction, tos_conceptual_ordering = (length [D], length (@nil Distinction)). ' + CL + '.' });

  // --- process_equiv и девятки (§ 1.8)
  fix('отношение `process_equiv` (обозначаемое `~~`), которое связывает два процесса, *сходящихся к одному пределу*', 'process_equiv', {
    claim: 'отношение `process_equiv` (обозначаемое `~~`), которое связывает два процесса, *расхождение которых с ростом стадии уходит ниже всякой точности*',
    note: DONE + ': было «сходящихся к одному пределу». ProcessCore.v:170: forall eps, 0 < eps -> exists N, forall n, N <= n -> Qabs (R1 n - R2 n) < eps. Сходимости определение не требует: equiv_does_not_require_convergence (' + EL + '), ' + CL + '.' });
  add({ theorem: 'equiv_iff_same_limit_when_one_converges', file: EL,
    claim: 'для процессов с рациональным пределом это и значит: *сходятся к одному пределу* (`equiv_iff_same_limit_when_one_converges`, файл `ProcessEquivLimit.v`);',
    note: 'equiv_iff_same_limit_when_one_converges : forall R1 R2 q, R1 ~~ const_process q -> (R1 ~~ R2 <-> R2 ~~ const_process q). ' + CL + '.' });
  fix('В этом языке позиция ToS по поводу $0{,}999…$ формулируется точно — и это удобный мост к будущей формализации.', null, {
    claim: 'В этом языке позиция ToS по поводу $0{,}999…$ формулируется точно — и в репозитории уже проверена.',
    note: DONE + ': было «удобный мост к будущей формализации». Формализация есть с 01.06.2026: ' + NP + ', теоремы nine_raw_lt_one и nine_equiv_one — ' + CL + '.' });
  fix('Запись $0{,}999…$ отвечает процессу $n ' + MAPSTO + ' 1 - 1/10^{ n+1}$; единица', 'nine_raw', {
    claim: 'Запись $0{,}999…$ отвечает процессу $n ' + MAPSTO + ' 1 - 1/10^{ n+1}$ (в файле `src/process/ProcessNinePoint.v` — `nine_raw`); единица отвечает постоянному процессу `const_process` $1$.',
    note: DONE + ': имя названо. ProcessNinePoint.v:66: Definition nine_raw : RealProcess := fun n => 1 - 1 / ten_pow (S n) — та же формула.' });
  const C_NINES = 'Формальная проверка этой картины в репозитории есть — файл `ProcessNinePoint.v`: теорема `nine_raw_lt_one` (на каждой стадии процесс девяток строго меньше единицы) и теорема `nine_equiv_one` (процесс девяток `process_equiv` `const_process` $1$), обе без аксиом;';
  fix('Формальная проверка этой картины — через теоремы вида', 'nine_raw_lt_one', {
    claim: C_NINES, page_price: 'без аксиом',
    note: DONE + ': было «самих этих теорем о девятках в репозитории пока нет». nine_raw_lt_one : forall n, nine_raw n < 1 (ProcessNinePoint.v:72). ' + CL + '.' });
  fix('Формальная проверка этой картины — через теоремы вида', 'nine_equiv_one', {
    claim: C_NINES, page_price: 'без аксиом',
    note: DONE + ': было «пока нет». nine_equiv_one : nine_raw ~~ const_process 1 (ProcessNinePoint.v:84). ' + CL + '.' });
  add({ theorem: 'nines_three_modes', file: EL,
    claim: 'три режима сведены в одну теорему `nines_three_modes` (файл `ProcessEquivLimit.v`). Их разбор относится к Части IV (Глава IV.3).',
    note: 'nines_three_modes : (forall n, nine_raw n < const_process 1 n) /' + BS + ' (forall n, ~ (nine_raw n == const_process 1 n)) /' + BS + ' nine_raw ~~ const_process 1. ' + CL + '. Отсылка верна: Глава IV.3, § 3.7.' });

  // --- разбор E/R/R, оговорка о статусе
  fix('онтологический порядок «$1$ прежде $0$» опирается на `distinction_order`', 'distinction_order', {
    claim: 'онтологический порядок «$1$ прежде $0$» в репозитории тоже *записан*, а не выведен — парой `distinction_order` (§ 1.2, § 1.4);',
    note: DONE + ': было «опирается на distinction_order». Definition distinction_order := (1%nat, 0%nat) — пара, вписанная рукой; страница теперь называет статус прямо.' });
  add({ theorem: 'conceptual_ordering_from_counts', file: CP,
    claim: 'что считают её компоненты — счёт одного совершённого акта и счёт пустого списка, — сказано теоремой `conceptual_ordering_from_counts` (файл `CountingPresence.v`).',
    note: 'conceptual_ordering_from_counts : forall D : Distinction, tos_conceptual_ordering = (length [D], length (@nil Distinction)); distinction_order = tos_conceptual_ordering (distinction_order_is_conceptual). ' + CL + '.' });
  save();
}

// ---------------------------------------------------------------- II.2 (имя свидетеля в § 2.4)
{
  const { fix, add, save } = open('part02-ch02');
  const LE = '$1 ' + BS + 'le 1$';
  fix('Доказательство предъявляет список из одного различия — `[distinction_of True]`', 'reflexivity', {
    claim: 'Доказательство предъявляет список из одного различия — `[distinction_true_false]`, список с единственным элементом, — и проверяет два условия: длина его равна единице (`reflexivity`), и ' + LE + ' (`lia`).',
    note: DONE + ' (развилка «свидетель» — А): имя свидетеля на странице приведено к исходнику. PrimalityOfOne.v: exists [distinction_true_false]. split; [reflexivity | lia]. Здесь reflexivity и lia — тактики.' });
  add({ theorem: 'first_count_is_one', file: PO,
    claim: 'exists [distinction_true_false].',
    note: 'Строка блока § 2.4 совпадает с исходником (PrimalityOfOne.v, доказательство first_count_is_one). ' + CL + '.' });
  save();
}
