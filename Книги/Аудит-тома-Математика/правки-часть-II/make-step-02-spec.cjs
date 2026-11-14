// Собирает описание правок шага 2 Части II (глава II.1 «Первичность единицы»; места 1.1, 1.3, 1.4, 1.6, 1.7, 1.8
// и блок роли-стороны со сноской 3): 12 правок. «Было» берётся с живой страницы.
// Запуск: node make-step-02-spec.cjs  -> шаг-02-глава-II1-асимметрия-и-порядки.txt (формат tools/apply-edits.cjs)
const fs = require('fs');
const path = require('path');
const LIVE = 'C:/Users/abary/quartz-put-mudrosti/content/Библиотека/';
const REL = 'Направления/Математика/Том Математика/02 Натуральные числа/01 Первичность единицы.md';
const page = fs.readFileSync(LIVE + REL, 'utf8').replace(/\r/g, '').split('\n');
function old(first, last, max) {
  const hits = page.filter((l) => l.startsWith(first)).length;
  const i = page.findIndex((l) => l.startsWith(first));
  if (i < 0 || hits !== 1) throw new Error('начало не найдено однозначно (' + hits + '): ' + first);
  let j = i; while (j < page.length && !page[j].startsWith(last)) j++;
  if (j >= page.length || j - i > (max || 20)) throw new Error('конец не найден: ' + last);
  return page.slice(i, j + 1);
}
function inline(prefix, a, b) {
  const o = old(prefix, prefix);
  if (o[0].split(a).length !== 2) throw new Error('фрагмент в строке не найден однозначно: ' + a.slice(0, 60));
  return { old: o, neu: [o[0].replace(a, () => b)] };
}
function whole(prefix, neu) { return { old: old(prefix, prefix), neu: [neu] }; }
const BS = String.fromCharCode(92);
const NEG = BS + 'neg';
const edits = [];

// 1. блок роли-стороны (стр. 284–288): предложение стало файлом; тип сторон взят из Binarity.v
edits.push({ old: old('Точнее это последнее утверждение формализуется не через', 'Inductive DistinctionSide := Marked | Unmarked.'),
  neu: ['Точнее это последнее утверждение формализуется не через',
        'доказательства, а через *роль-сторону* — так (файл',
        '`DistinctionSideRole.v`; тип сторон `Side := Marked | Unmarked`',
        'взят из `Binarity.v`):',
        '',
        '```coq',
        'Definition DistinctionSide : Set := Side.'] });
// 2. сноска 3
edits.push(whole('[^3]: Тип `DistinctionSide` и `side_value` в текущем репозитории отсутствуют',
  '[^3]: Это усиление внесено: `DistinctionSide`, `side_value` и теорема `marked_role_gt_unmarked_role` — в файле `DistinctionSideRole.v` (тип сторон `Side` взят из `Binarity.v`). Там же доказано, что `mark` и `unmark` возвращают именно эти значения ролей (`mark_is_marked_value`, `unmark_is_unmarked_value`), что из двух ролей всякого различения выполнена ровно одна (`exactly_one_side_holds`) и что пара `distinction_order` есть пара значений двух ролей (`distinction_order_from_roles`). Само сопоставление «маркированной — $1$, немаркированной — $0$» остаётся определением — записью прочтения, а не выводом.'));
// 3. блок distinction_asymmetric (стр. 347): комментарий о classic
edits.push(whole('Proof. (* ... uses classic ... *) Qed.', 'Proof. (* ... *) Qed.'));
// 4. сноска 4: цена
edits.push(whole('[^4]: Доказательство `distinction_asymmetric` опирается на аксиому `classic`',
  '[^4]: Утверждение `distinction_asymmetric` — «$P$ и $' + NEG + ' P$ не совпадают» — доказано без допущений (до 13.11.2026 доказательство шло через аксиому `classic`, но утверждению она не нужна). В общей форме — для всякого различения, а не только канонического — то же дают `swap_changes_positive_of_any` (тот же файл) и `sides_distinct` (файл `DistinctionCoDefinition.v`): различность сторон следует из двух правил записи, несовместности ($L2$) и исчерпанности ($L3$ для сторон). Закон $L3$ участвует здесь как правило самой записи, а не как аксиома `classic`.'));
// 5. § 1.4.2 (стр. 786–787): где зафиксирована различённость порядков
edits.push({ old: old('В репозитории оба порядка присутствуют явно, и их различённость', 'зафиксирована формально. Файл `AsymmetricDistinction.v`'),
  neu: ['В репозитории оба порядка присутствуют явно, и их различённость',
        'зафиксирована формально (теорема `orderings_dual_pairs`, см. ниже).',
        'Файл `AsymmetricDistinction.v`'] });
// 6. там же (стр. 838–844): где записана двойственность пар
edits.push({ old: old('неравенству $0 < 1$. Поэтому *формальная* запись двойственности', '(`tos_first`) сопоставлено единице, а не нулю.[^5]'),
  neu: ['неравенству $0 < 1$. *Формальная* запись двойственности',
        'двух порядков как пары $(1,0)$ против пары $(0,1)$ дана в том же файле',
        'отдельно: пары `tos_conceptual_ordering` $:= (1,0)$ и',
        '`number_ordering` $:= (0,1)$ и теорема `orderings_dual_pairs` —',
        'пары зеркальны и различны; пара `distinction_order` из',
        '`AsymmetricDistinction.v` есть первая из них',
        '(`distinction_order_is_conceptual`). Имена `tos_first` и',
        '`tos_absence` регистрируют ту же мысль в более слабой',
        'форме: числовой порядок $0 < 1$ налицо, и онтологическое имя начала',
        '(`tos_first`) сопоставлено единице, а не нулю.[^5]'] });
// 7. сноска 5
edits.push(whole('[^5]: Это расхождение формы — предмет для синхронизации репозитория.',
  '[^5]: Эта синхронизация внесена 13.11.2026: пары `tos_conceptual_ordering` $:= (1,0)$ и `number_ordering` $:= (0,1)$ и теорема `orderings_dual_pairs` — в `PrimalityOfOne.v`; `orderings_dual` оставлена как есть. Обе пары вписаны рукой: теорема говорит об этих двух записях — что они зеркальны и различны, — а не выводит порядок обоснования. Что считают компоненты пары $(1,0)$, сказано теоремой `conceptual_ordering_from_counts` (файл `CountingPresence.v`): первая — счёт одного совершённого акта, вторая — счёт пустого списка.'));
// 8. § 1.4.3 (стр. 878–879): tos_ordering
edits.push({ old: old('нуль как границу; `tos_ordering`, задающее порядок', 'обоснования. Синтаксис Rocq остаётся нетронутым; меняется'),
  neu: ['нуль как границу; `tos_ordering`, сохраняющее при этом чтении',
        'числовой порядок $0 < 1$; пара `tos_conceptual_ordering`, записывающая',
        'порядок обоснования. Синтаксис Rocq остаётся нетронутым; меняется'] });
// 9. § 1.8 (стр. 1768): что связывает process_equiv
edits.push(whole('которое связывает два процесса, *сходящихся к одному пределу*;',
  ['которое связывает два процесса, *расхождение которых с ростом стадии',
   'уходит ниже всякой точности*, — для процессов с рациональным пределом',
   'это и значит: *сходятся к одному пределу*',
   '(`equiv_iff_same_limit_when_one_converges`, файл `ProcessEquivLimit.v`);'].join('\n')));
// 10. там же: девятки — «мост к будущей формализации»
edits.push({ old: old('точно — и это удобный мост к будущей формализации. Запись', '$n ' + BS + 'mapsto 1 - 1/10^{ n+1}$; единица отвечает постоянному процессу'),
  neu: ['точно — и в репозитории уже проверена. Запись',
        '$0{,}999…$ отвечает процессу',
        '$n ' + BS + 'mapsto 1 - 1/10^{ n+1}$ (в файле `src/process/ProcessNinePoint.v` —',
        '`nine_raw`); единица отвечает постоянному процессу'] });
// 11. там же: «теорем о девятках в репозитории пока нет»
edits.push({ old: old('законно, потому что запись уже означает класс или предел. Формальная', 'язык, но самих этих теорем о девятках в репозитории пока нет.'),
  neu: ['законно, потому что запись уже означает класс или предел. Формальная',
        'проверка этой картины в репозитории есть — файл',
        '`ProcessNinePoint.v`: теорема `nine_raw_lt_one` (на каждой стадии',
        'процесс девяток строго меньше единицы) и теорема `nine_equiv_one`',
        '(процесс девяток `process_equiv` `const_process` $1$), обе без',
        'аксиом; три режима сведены в одну теорему `nines_three_modes` (файл',
        '`ProcessEquivLimit.v`). Их разбор относится к Части IV (Глава IV.3).'] });
// 12. разбор E/R/R, оговорка о статусе (стр. 1832–1833): на что «опирается» порядок
edits.push({ old: old('*доказывает* первичность, и онтологический порядок «$1$ прежде', '$0$» опирается на `distinction_order` (§ 1.2, § 1.4).'),
  neu: ['*доказывает* первичность, и онтологический порядок «$1$ прежде',
        '$0$» в репозитории тоже *записан*, а не выведен — парой',
        '`distinction_order` (§ 1.2, § 1.4); что считают её компоненты — счёт',
        'одного совершённого акта и счёт пустого списка, — сказано теоремой',
        '`conceptual_ordering_from_counts` (файл `CountingPresence.v`).'] });

const out = ['@@FILE ' + REL];
for (const e of edits) out.push('@@OLD', ...e.old, '@@NEW', ...e.neu, '@@END');
fs.writeFileSync(path.join(__dirname, 'шаг-02-глава-II1-асимметрия-и-порядки.txt'), out.join('\n') + '\n');
console.log('описание собрано: правок ' + edits.length);
