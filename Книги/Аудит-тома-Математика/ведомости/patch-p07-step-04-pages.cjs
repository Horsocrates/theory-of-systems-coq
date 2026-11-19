// Часть VII, шаг 4, страницы (2026-11-18, слово автора «Делай, вариант 1»): 23 правки главы VII.3 внесены
// (дискретная ортогональность над любым носителем; вырождение над Q; DFT при N = 3, 4; статус i и ω — по главе XI:
//  Элемент-роли конечного порядка; сноски 1, 2, 3 и новая 5).
// Формализация — новый src/process/ProcessDiscreteCharacters.v; прежние файлы не менялись.
// Запуск: node patch-p07-step-04-pages.cjs  (затем relocate + merge по part07-ch03). Скрипт повторяем.
// Внимание: строки с настоящим знаком параграфа через L() не пропускать.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 18.11 (Часть VII, шаг 4, слово автора: вариант 1)';
const CL = 'Closed under the global context';
const DC = 'src/process/ProcessDiscreteCharacters.v';
const DT = 'src/process/ProcessDiscreteTrig.v';
const BS = String.fromCharCode(92);
const L = (s) => s.split('§').join(BS);   // «§» — обратная косая черта
const AND = '/' + BS;
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

function open(name) {
  const p = path.join(__dirname, name + '.json');
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  const pick = (prefix, th, file) => {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix)
      && (th === undefined || (th === null ? !r.theorem : r.theorem === th))
      && (file === undefined || r.file === file));
    if (hit.length > 1) throw new Error(name + ': не одна запись: ' + prefix + ' / ' + th);
    return hit[0];
  };
  const fix = (prefix, th, fields, file) => { const r = pick(prefix, th, file); if (!r) return; Object.assign(r, { verdict: 'ok' }, fields); n++; };
  const add = (rec) => {
    if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && (r.file || null) === (rec.file || null) && norm(r.claim) === norm(rec.claim))) return;
    j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
  };
  const save = () => {
    const seen = new Set(); const before = j.records.length;
    j.records = j.records.filter((r) => { const k = (r.theorem || '') + '|' + (r.file || '') + '|' + norm(r.claim); if (seen.has(k)) return false; seen.add(k); return true; });
    if (before !== j.records.length) console.log(name + '.json: снято дублей ' + (before - j.records.length));
    fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
    console.log(name + '.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length + ', не «верно» ' + j.records.filter((r) => r.verdict !== 'ok').length);
  };
  return { j, fix, add, save };
}

// --- утверждения (номера строк — src/process/ProcessDiscreteCharacters.v, если не сказано иное)
const N_GEN = "discrete_orthogonality_gen : для носителя R с отношением req (рефлексивным, транзитивным), сложением radd, согласованным с req, и умножением rmul; для chi : nat -> nat -> R с посылками (1) req (chi 0 j) rI, (2) req (rmul (chi k j) (chi k' j)) (chi (k + k') j), (3) 0 < m -> m < N -> req (r_sum (fun j => chi m j) N) rO — forall k k', k + k' < N -> req (r_sum (fun j => rmul (chi k j) (chi k' j)) N) (if (k + k' =? 0) then r_sum (fun _ => rI) N else rO) (:226); r_sum — конечная сумма в носителе (:204). " + CL + '.';
const N_FZ = 'chi_forced_zero : forall N (chi : nat -> nat -> Q), 3 <= N -> (forall j, chi 0 j == 1) -> (forall k k\' j, chi k j * chi k\' j == chi (k + k\') j) -> (forall m, 0 < m -> m < N -> q_sum (fun j => chi m j) N == 0) -> forall m j, 0 < m -> j < N -> chi m j == 0 (:69); из (2) и (3) при m = 2: Σ_j chi(1,j)² = 0. ' + CL + '.';
const N_FZB = 'chi_forced_zero_bounded (:90): то же при посылке (2), суженной до k + k\' < N, — для 0 < m < N. ' + CL + '.';
const N_SQ0 = 'char_square_sum_zero (:124): из трёх посылок при 0 < k, k + k < N — q_sum (fun j => chi k j * chi k j) N == 0; orthogonality_terms_zero (:110): при N >= 3 каждое слагаемое суммы теоремы равно нулю, кроме k = k\' = 0. ' + CL + '.';
const N_TRIV = 'chi_triv_model (:143): семейство chi_triv k j := if k =? 0 then 1 else 0 (:141) удовлетворяет трём посылкам при всяком N. ' + CL + '.';
const N_W = 'chi_w_model (:168): при N = 2 трём посылкам удовлетворяет знаковый характер chi_w k j := (−1)^{k j} (:160); chi_w_nonzero (:179); chi_w_norm_11 (:184): Σ_j chi_w 1 j · chi_w 1 j == 2 — пара (1, 1) вне диапазона теоремы. ' + CL + '.';
const N_C4 = "chi4_model (:306): для chi4 k j := i_pow (k * j) (:301; i_pow — степени мнимой единицы qi_i, :282) над гауссовыми рациональными Qi — (1) qi_eq (chi4 0 j) qi_one, (2) qi_eq (qi_mul (chi4 k j) (chi4 k' j)) (chi4 (k + k') j), (3) 0 < m -> m < 4 -> qi_eq (qi_sum (fun j => chi4 m j) 4) qi_zero; chi4_nonzero (:320). " + CL + '.';
const N_C3 = "chi3_model (:393): для chi3 k j := w_pow (k * j) (:389; w_pow — степени ω, :356) над числами Эйзенштейна GQw — три посылки при N = 3; chi3_nonzero (:407). " + CL + '.';
const N_H4 = "dft4_hermitian : forall k k', k < 4 -> k' < 4 -> qi_eq (qi_sum (fun j => qi_mul (chi4 k j) (qi_conj (chi4 k' j))) 4) (if (k =? k') then mkQi 4 0 else qi_zero) (:339); билинейная форма — dft4_bilinear (:324), из discrete_orthogonality_gen. " + CL + '.';
const N_H3 = "dft3_hermitian : forall k k', k < 3 -> k' < 3 -> gw_eq (gw_sum (fun j => gwmul (chi3 k j) (gwconj (chi3 k' j))) 3) (if (k =? k') then (3, 0) else gw0) (:423); билинейная форма — dft3_bilinear (:411). " + CL + '.';
const N_I = 'imaginary_unit_is_element (stdlib/GaussianMUB.v:103): gi — пара (0, 1) с i² = −1 и i⁴ = 1; qi_i := mkQi 0 1 (process/ProcessGaussianQ.v:42), qi_i_squared (:58). ' + CL + '.';
const N_OM = 'omega_is_element (stdlib/EisensteinMUB.v:67): gww — пара (0, 1) в ℚ[ω] с ω³ = 1 и 1 + ω + ω² = 0; fourier_orthogonality (:123): трёхточечный базис (1,1,1), (1,ω,ω²), (1,ω²,ω) ортогонален. ' + CL + '.';

{
  const { fix, add, save } = open('part07-ch03');
  // --- правка 1: что доказано в главе
  fix('Доказанный результат главы условный', 'discrete_orthogonality', { theorem: 'discrete_orthogonality_gen', file: DC,
    claim: 'Доказанный результат главы таков: дискретная ортогональность есть конечная теорема о *любом* носителе значений, в котором выполнены три свойства характеров.',
    note: DONE + ': было «если принять одно свойство корней единицы, то дискретная ортогональность становится конечной теоремой над ℚ… трансцендентность сжата в одну посылку» — посылок три, и над ℚ при N >= 3 им удовлетворяют только нулевые характеры. ' + N_GEN });
  const C22 = L('Над самим ℚ при $N§ge3$ этим свойствам удовлетворяют только нулевые характеры, и это доказано; над конечными расширениями ℚ[i] ($N=4$) и ℚ[ω] ($N=3$), где корни единицы суть пары рациональных чисел, им удовлетворяют настоящие характеры DFT, и ортогональность доказана полностью, с сопряжением.');
  for (const [th, nt] of [['chi_forced_zero', N_FZ], ['chi4_model', N_C4], ['chi3_model', N_C3], ['dft4_hermitian', N_H4], ['dft3_hermitian', N_H3]]) add({ theorem: th, file: DC, claim: C22, note: nt });
  // --- правка 2: три уровня
  fix('*Первый* — доказанный над ℚ:', 'discrete_orthogonality', { theorem: 'discrete_orthogonality_gen', file: DC,
    claim: '*Первый* — доказанный: дискретная ортогональность характеров *при явно названных алгебраических гипотезах* (значение на нулевой частоте, характер как гомоморфизм, зануляющаяся геометрическая сумма) над любым носителем значений, и её примеры — DFT при $N=4$ над ℚ[i] и при $N=3$ над ℚ[ω]; это конечные теоремы, 0 аксиом.[^1]',
    note: DONE + ': было «доказанный над ℚ… (характер как гомоморфизм плюс зануляющаяся геометрическая сумма)» — названы все три посылки; носитель произвольный. ' + N_GEN + ' Примеры: ' + N_H4 + ' ' + N_H3 });
  fix('*Третий* — честная P4-граница, которую ToS *не* строит: сами значения', 'imaginary_unit_is_element', { theorem: null, file: null,
    claim: L('*Третий* — честная P4-граница, которую ToS *не* строит: сами значения $§sin/§cos$ в общих точках, корни единицы $e^{2§pi ik/N}$ общего порядка $N$, поле $ℂ$, континуум-интеграл как готовый объект и завершённый бесконечный ряд Фурье.'),
    note: DONE + ': из перечня сняты мнимая единица и корни единицы порядков 3 и 4 (в формализации они построены). Статус: функций sin и cos, корней единицы общего порядка, поля ℂ над процессными вещественными, завершённого интеграла и завершённого ряда в src нет.' });
  const C34 = L('Мнимая единица $i$ и кубический корень $§omega$ в эту границу не входят: они построены парами рациональных чисел (Часть XI: Элемент-роли конечного порядка).');
  add({ theorem: 'imaginary_unit_is_element', file: 'src/stdlib/GaussianMUB.v', claim: C34, note: N_I });
  add({ theorem: 'omega_is_element', file: 'src/stdlib/EisensteinMUB.v', claim: C34, note: N_OM });
  fix('Первый уровень ведём как условно доказанный', 'discrete_orthogonality', { theorem: 'discrete_orthogonality_gen', file: DC,
    claim: 'Первый уровень ведём как доказанный при явных гипотезах о характерах, второй — как процесс, третий — как явно помеченную границу.' });
  // --- правка 5: значения нерациональны; при N = 3, 4 построены
  fix(L('характеры живут в $ℂ^N$, полноценного поля $ℂ$'), null, {
    claim: L('характеры живут в $ℂ^N$, полноценного поля $ℂ$ как уже построенного носителя над процессными вещественными ToS не строит, а корень единицы $§omega^{kj}$ в общем случае иррационален и комплексен.') });
  const C128 = 'При $N=4$ и $N=3$ хватает конечных расширений ℚ[i] и ℚ[ω] — пар рациональных чисел,— и там характеры построены.[^2]';
  add({ theorem: 'chi4_model', file: DC, claim: C128, note: N_C4 });
  add({ theorem: 'chi3_model', file: DC, claim: C128, note: N_C3 });
  // --- правка 6: курсив о скелете
  const C131 = L('Алгебраический скелет (зануляющаяся сумма) от носителя не зависит: он доказан для любых значений с нужными законами, но рациональных значений с этими законами при $N§ge3$ нет, кроме нулевых;');
  fix('Алгебраический скелет (зануляющаяся сумма) становится рациональным', 'discrete_orthogonality', { theorem: 'discrete_orthogonality_gen', file: DC, claim: C131,
    note: DONE + ': было «становится рациональным, если значения характеров заменить абстрактными рациональными параметрами с нужными законами» — такие параметры при N >= 3 обязаны быть нулями. ' + N_GEN });
  add({ theorem: 'chi_forced_zero', file: DC, claim: C131, note: N_FZ });
  // --- правки 7–9: три свойства и теорема
  fix(L('Возьмём значения характеров $§chi(k,j)$ как *абстрактные* рациональные параметры'), null, { file: DC,
    claim: L('Возьмём значения характеров $§chi(k,j)$ как *абстрактные* элементы какого-либо носителя со сложением и умножением (не строя $e^{2§pi ikj/N}$) и потребуем от них лишь трёх свойств:'),
    note: DONE + ': значения — элементы носителя R (раздел DiscreteCharGen, :198–242); в ProcessDiscreteTrig.v они рациональны.' });
  fix('Свойства (1)–(2) чисто алгебраические; за пределы ℚ выходит *только* свойство (3)', 'discrete_orthogonality', { theorem: 'chi_triv_model', file: DC,
    claim: 'Каждое свойство порознь выполнимо и над ℚ; свойство (3) — абстрактная форма факта «сумма корней единицы равна нулю».',
    note: DONE + ': было «за пределы ℚ выходит только свойство (3)» — все три свойства суть равенства о значениях и над ℚ выполнимы (вместе — тривиальным семейством). ' + N_TRIV });
  const C151 = L('Вместе же над ℚ при $N§ge3$ они оставляют только нулевые характеры: из (2) и (3) следует $§sum_j§chi(1,j)^2=0$.');
  add({ theorem: 'chi_forced_zero', file: DC, claim: C151, note: N_FZ });
  add({ theorem: 'char_square_sum_zero', file: DC, claim: C151, note: N_SQ0 });
  fix('И вот при этих гипотезах дискретная ортогональность есть конечная теорема над ℚ', 'discrete_orthogonality', { theorem: 'discrete_orthogonality_gen', file: DC,
    claim: "И при этих гипотезах дискретная ортогональность есть конечная теорема над любым носителем (в диапазоне $k+k'<N$):",
    note: DONE + ': ' + N_GEN + ' Рациональная теорема discrete_orthogonality (ProcessDiscreteTrig.v:63) — её частный случай: discrete_orthogonality_Q_from_gen (:246).' });
  fix('доказанная чистой рациональной алгеброй.[^3]', 'discrete_orthogonality', { theorem: 'discrete_orthogonality_gen', file: DC,
    claim: L("доказанная чистой алгеброй: нужны лишь три гипотезы и согласованность сложения с равенством.[^3] Полная модульная DFT-формула $k+k'§equiv0§pmod N$ потребовала бы арифметики индексов по модулю $N$, которую общая теорема не строит; в доказанном диапазоне $k+k'<N$ условие $k+k'§equiv0$ совпадает с $k+k'=0$."),
    note: DONE + ': посылки носителя — рефлексивность и транзитивность req, согласованность radd с req (:205–208); диапазон теоремы k + k\' < N. ' + CL + '.' });
  fix('В классическом DFT это читается как ортогональность с обратным характером', null, {
    claim: L("В классическом DFT это читается как ортогональность с обратным характером $k'=-k§pmod N$, обычно реализуемая комплексным сопряжением.") });
  const C166 = L("Для двух размеров она доказана полностью: при $N=4$ над ℚ[i] и при $N=3$ над ℚ[ω] характеры $i^{kj}$ и $§omega^{kj}$ удовлетворяют трём гипотезам, и $§sum_j§chi_k(j)§,§overline{§chi_{k'}(j)}=N§delta_{kk'}$ при всех $k,k'<N$.[^5]");
  add({ theorem: 'dft4_hermitian', file: DC, claim: C166, note: N_H4 });
  add({ theorem: 'dft3_hermitian', file: DC, claim: C166, note: N_H3 });
  // --- правка 10: итоговый курсив
  fix('*Файл-граница ничего трансцендентного не строит', 'discrete_orthogonality', { theorem: 'discrete_orthogonality_gen', file: DC,
    claim: '*Теорема-граница ничего трансцендентного не строит: она показывает, что ортогональность DFT есть алгебра характеров при трёх явных гипотезах, а выход за пределы ℚ сосредоточен в носителе значений. Там, где носитель — конечное расширение ℚ ($N=3$, $N=4$), граница пройдена: характеры построены, ортогональность доказана.*',
    note: DONE + ': было «вся ортогональность DFT есть рациональная алгебра характеров плюс один вход… Граница сжата в единственную явную гипотезу» — гипотез три, а над ℚ они вырождены. ' + N_GEN + ' ' + N_H4 + ' ' + N_H3 });
  // --- правка 13: постановка разбора
  fix('Оговорка об уровне: формальный объект здесь один', 'discrete_orthogonality', { theorem: 'discrete_orthogonality_gen', file: DC,
    claim: 'Оговорка об уровне: формальных объектов здесь два — условная теорема дискретной ортогональности при явных гипотезах и её примеры, DFT при $N=3$ и $N=4$; прочее (непрерывная тригонометрия, DFT общего порядка) присутствует как *граница*, помеченная, а не построенная.',
    note: DONE + ': теорема — discrete_orthogonality_gen (:226) и discrete_orthogonality (ProcessDiscreteTrig.v:63); примеры — chi4_model (:306), dft4_hermitian (:339), chi3_model (:393), dft3_hermitian (:423). ' + CL + '.' });
  // --- правка 14: Роли (развилка, вариант 1)
  const C223 = L('Мнимая единица $i$ и кубический корень $§omega$ — Элемент-роли конечного порядка (Часть XI): они построены парами рациональных чисел; корни единицы общего порядка — того же рода, но здесь не построены.');
  fix(L('А сами значения $§sin/§cos$, $e^{2§pi ik/N}$, мнимая единица $i$'), 'omega_is_element', { claim: C223,
    note: DONE + ': было «значения sin/cos, e^{2πik/N}, мнимая единица i, число π, континуум-интеграл — роль-пределы… которые ToS не актуализирует». Автор выбрал чтение главы XI (XI.1, XI.4: i и ω — Элемент-роли конечного порядка). ' + N_OM });
  add({ theorem: 'imaginary_unit_is_element', file: 'src/stdlib/GaussianMUB.v', claim: C223, note: N_I });
  add({ theorem: null, file: null, claim: L('А значения $§sin/§cos$, число $§pi$, континуум-интеграл — роль-пределы: места, к которым процессы стремятся, но которые ToS не актуализирует.'),
    note: 'статус: функций sin и cos, числа π как завершённого объекта и завершённого интеграла в src нет; слова страницы формализации не противоречат.' });
  // --- правка 17: проверка сформированности
  const C244 = 'Условная теорема не делает вид, что построила корни единицы общего порядка — она показывает, что *при* трёх свойствах характеров ортогональность есть чистая алгебра; а там, где корни построены ($N=3$, $N=4$), сами свойства доказаны.';
  fix('Условная теорема не делает вид, что построила корни единицы — она показывает', 'discrete_orthogonality', { theorem: 'discrete_orthogonality_gen', file: DC, claim: C244,
    note: DONE + ': было «при их ключевом свойстве вся ортогональность рациональна». ' + N_GEN });
  add({ theorem: 'chi4_model', file: DC, claim: C244, note: N_C4 });
  add({ theorem: 'chi3_model', file: DC, claim: C244, note: N_C3 });
  // --- сноска 1
  fix('Опорный файл — `ProcessDiscreteTrig.v` (каталог', null, {
    claim: 'Опорные файлы (каталог `src/process/`) — `ProcessDiscreteTrig.v` (2 доказанных утверждения; значения характеров рациональны) и `ProcessDiscreteCharacters.v` (30 утверждений: общий носитель значений и примеры); оба — 0 `Admitted`, 0 аксиом.' });
  add({ theorem: null, file: DC, page_price: '0 аксиом', assumptions: 'все 41 объявление файла: ' + CL,
    claim: 'Опорные файлы (каталог `src/process/`) — `ProcessDiscreteTrig.v` (2 доказанных утверждения; значения характеров рациональны) и `ProcessDiscreteCharacters.v` (30 утверждений: общий носитель значений и примеры); оба — 0 `Admitted`, 0 аксиом.',
    note: 'В ProcessDiscreteCharacters.v 30 строк Qed и одиннадцать определений; Admitted, Axiom, Parameter нет; все объявления — ' + CL + '.' });
  fix('Он *не* строит', null, { file: DC,
    claim: L('Они *не* строят $§sin/§cos$, поле $ℂ$ или формулу Эйлера; они формализуют, *какие гипотезы* превращают ортогональность характеров в утверждение о конечной сумме и где эти гипотезы выполнены.'),
    note: DONE + ': было «он формализует, какие гипотезы превращают тригонометрическую ортогональность в утверждение о конечной сумме» — над ℚ гипотезам удовлетворяют только нулевые характеры (chi_forced_zero, :69). Теперь названо, где гипотезы выполнены: chi4_model (:306), chi3_model (:393). В файлах нет sin/cos, поля ℂ и формулы Эйлера.' });
  // --- сноска 2
  const C2 = L('Значения $e^{2§pi ik/N}$ — алгебраические числа: при $N=4$ это $§pm1,§pm i$, при $N=3$ — $1,§omega,§omega^2$, и они построены парами рациональных — `qi_i` (`ProcessGaussianQ.v`), `omega_is_element` (`EisensteinMUB.v`; там же ортогональность трёхточечного базиса, `fourier_orthogonality`).');
  fix('комплексные потребовали бы пар таких процессов, но дело не в паре', 'fourier_orthogonality', { claim: C2,
    note: DONE + ': было «e^{2πik/N} трансцендентно. Поэтому комплексный DFT — роль-предел, а не построенный объект» — корни единицы алгебраичны, а при N = 3, 4 построены. ' + N_OM });
  add({ theorem: 'omega_is_element', file: 'src/stdlib/EisensteinMUB.v', claim: C2, note: N_OM });
  add({ theorem: 'qi_i', file: 'src/process/ProcessGaussianQ.v', claim: C2, note: 'qi_i := mkQi 0 1 (ProcessGaussianQ.v:42) — мнимая единица как пара рациональных; qi_i_squared : qi_eq (qi_mul qi_i qi_i) (mkQi (-(1)) 0) (:58). ' + CL + '.' });
  add({ theorem: null, file: null, claim: 'Для общего $N$ нужного расширения ℚ в формализации нет: DFT общего порядка не построен.',
    note: 'статус: в src построены ℚ[i] (ProcessGaussianQ.v, stdlib/GaussianMUB.v) и ℚ[ω] (stdlib/EisensteinMUB.v); круговых расширений ℚ[ζ_N] для общего N нет.' });
  // --- сноска 3
  fix('В `ProcessDiscreteTrig.v`: `char_sum_full`', 'char_sum_full', {
    claim: 'В `ProcessDiscreteTrig.v` (значения в ℚ): `char_sum_full` (нулевая частота суммируется в $N$, из (1) и суммы констант)' });
  fix(L('`discrete_orthogonality` ($§sum_{j<N}§chi(k,j)§chi(k'), 'discrete_orthogonality', {
    claim: L("`discrete_orthogonality` ($§sum_{j<N}§chi(k,j)§chi(k',j)=N$ при $k+k'=0$, иначе $0$, для $k+k'<N$).") });
  add({ theorem: 'discrete_orthogonality_gen', file: DC, claim: L("Над любым носителем — `discrete_orthogonality_gen` (`ProcessDiscreteCharacters.v`). Доказательство: гомоморфизм (2) сворачивает произведение в $§chi(k+k',j)$, далее (1) или (3)."), note: N_GEN });
  const C3 = L("Над ℚ при $N§ge3$ гипотезы оставляют только нулевые характеры — `chi_forced_zero` (то же при гомоморфизме, суженном до $k+k'<N$, — `chi_forced_zero_bounded`); при $N=2$ им удовлетворяет знаковый характер Уолша — `chi_w_model`. 0 аксиом.");
  fix('0 аксиом — трансцендентность в гипотезе (3), а не в аксиоме.', 'discrete_orthogonality', { theorem: 'chi_forced_zero', file: DC, claim: C3,
    note: DONE + ': было «трансцендентность в гипотезе (3)» — гипотеза (3) есть рациональное равенство и содержания корней единицы не несёт. ' + N_FZ });
  add({ theorem: 'chi_forced_zero_bounded', file: DC, page_price: '0 аксиом', claim: C3, note: N_FZB });
  add({ theorem: 'chi_w_model', file: DC, page_price: '0 аксиом', claim: C3, note: N_W });
  // --- сноска 5
  const F5a = L("`ProcessDiscreteCharacters.v`. $N=4$, носитель ℚ[i] (`ProcessGaussianQ.v`): характеры $§chi_k(j)=i^{kj}$ удовлетворяют трём гипотезам — `chi4_model`; общая теорема на них — `dft4_bilinear`; ортогональность с сопряжением при всех $k,k'<4$ — `dft4_hermitian`.");
  for (const [th, nt] of [['chi4_model', N_C4], ['dft4_bilinear', N_H4], ['dft4_hermitian', N_H4]]) add({ theorem: th, file: DC, claim: F5a, note: nt });
  const F5b = '$N=3$, носитель ℚ[ω] (`EisensteinMUB.v`): `chi3_model`, `dft3_bilinear`, `dft3_hermitian`.';
  for (const [th, nt] of [['chi3_model', N_C3], ['dft3_bilinear', N_H3], ['dft3_hermitian', N_H3]]) add({ theorem: th, file: DC, claim: F5b, note: nt });
  const F5c = 'Характеры ненулевые: `chi4_nonzero`, `chi3_nonzero`. 0 аксиом.';
  add({ theorem: 'chi4_nonzero', file: DC, page_price: '0 аксиом', claim: F5c, note: N_C4 });
  add({ theorem: 'chi3_nonzero', file: DC, page_price: '0 аксиом', claim: F5c, note: N_C3 });
  save();
}
