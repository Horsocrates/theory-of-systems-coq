// Часть IX, шаг 5, страницы (2026-11-23, слово автора «Делай»): 10 правок главы IX.5 внесены по вариантам 1
// развилок 2 и 3 (два измерения — названа теорема о связях без вытяжения, двумерность оставлена чтением; три
// измерения — условием названа оценка нелинейного члена в инвариантной области).
// Формализация — новые src/navier_stokes/GalerkinEnergyEstimate.v и GalerkinEnstrophyRegion.v; прежние файлы не
// менялись.
// Запуск: node patch-p09-step-05-pages.cjs  (затем relocate + merge по part09-ch05). Повторяем.
// Внимание: L() превращает знак «¤» в обратную косую черту.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 23.11 (Часть IX, шаг 5, слово автора)';
const KEPT = DONE + ' (формализацией; текст фразы не менялся): ';
const CL = 'Closed under the global context';
const GE = 'src/navier_stokes/GalerkinEnergyEstimate.v';
const ER = 'src/navier_stokes/GalerkinEnstrophyRegion.v';
const EE = 'src/navier_stokes/EnergyEstimate.v';
const TI = 'src/navier_stokes/TriadicInteraction.v';
const IR = 'src/navier_stokes/InvariantRegion.v';
const AS = 'src/navier_stokes/AttackSynthesis.v';
const VO = 'src/navier_stokes/Vorticity.v';
const CB = 'src/navier_stokes/ConcentrationBound.v';
const BS = String.fromCharCode(92);
const L = (s) => s.split('¤').join(BS);   // «¤» — обратная косая черта
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

// --- утверждения (номера строк — по src)
const N_APR = L('galerkin_traj_energy_apriori : forall nu B K dt M (a0 : modal_state), energy_conserving B K -> 0 <= nu -> 0 <= dt -> (forall k l m, (k < K)%nat -> (l < K)%nat -> (m < K)%nat -> Qabs (B k l m) <= M) -> 2 * dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 -> 4 * dt * (M * M) * (Kq * Kq * Kq) * modal_energy K a0 <= nu -> energy_decreasing K (gtraj nu B K dt a0) /¤ (forall n, modal_energy K (gtraj nu B K dt a0 n) <= modal_energy K a0) (GalerkinEnergyEstimate.v:444); Kq = inject_Z (Z.of_nat K); energy_conserving (:104) — нелинейный член работы не совершает; для связи adv T — adv_traj_energy_apriori (:474). На состояния условий нет; условие стоит на шаг. ') + CL + '.';
const N_GROW = 'galerkin_euler_energy_can_grow : modal_energy 2 a_unit < modal_energy 2 (gstep (1#100) (adv T_pair) 2 1 a_unit) (GalerkinEnergyEstimate.v:165). ' + CL + '.';
const N_PREM = 'energy_bound_needs_premise : ~ (forall K (u : time_series) n, energy_at K u n <= energy_at K u 0) (GalerkinEnergyEstimate.v:87); свидетель — u_grow (:85); u_grow_not_decreasing (:94). ' + CL + '.';
const N_FORM = 'formal_traj_energy_decreasing : forall (nsc : NSCoupling) nu K dt (a0 : modal_state), 0 <= nu -> 0 <= dt -> dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 -> energy_decreasing K (gtraj nu B_coeff K dt a0) (GalerkinEnergyEstimate.v:506); для вязкой ломаной euler_evolve прежнего файла — viscous_euler_energy_decreasing (:554). ' + CL + '.';
const N_EBI = 'Theorem energy_bounded_by_initial : forall K u, energy_decreasing K u -> forall n, energy_at K u n <= energy_at K u 0 (EnergyEstimate.v:73); energy_monotone (:84) — то же между любыми двумя шагами. u : time_series — произвольная последовательность состояний; записи NSCoupling теоремы не получают. ' + CL + '.';
const N_ED = 'Definition energy_decreasing (K : nat) (u : time_series) : Prop := forall n, energy_at K u (S n) <= energy_at K u n (EnergyEstimate.v:45). Для траекторий схемы посылка доказана: galerkin_traj_energy_apriori (GalerkinEnergyEstimate.v:444), formal_traj_energy_decreasing (:506).';
const N_CR = 'Definition conditionally_regular (K : nat) (u : time_series) (nu C_stretch : Q) : Prop := forall n, enstrophy_at K u n < critical_enstrophy nu C_stretch -> enstrophy_at K u (S n) <= enstrophy_at K u n (EnergyEstimate.v:248).';
const N_R3D = 'Theorem regularity_3d_small_data : forall K u nu C_stretch, conditionally_regular K u nu C_stretch -> enstrophy_at K u 0 < critical_enstrophy nu C_stretch -> forall n, enstrophy_at K u n < critical_enstrophy nu C_stretch (EnergyEstimate.v:255) — индукция по посылке; последовательность u произвольна. ' + CL + '.';
const N_NS = L('no_stretching_traj_apriori : forall nu B K dt M (a0 : modal_state), energy_conserving B K -> (forall a : nat -> Q, stretch B K a == 0) -> 0 <= nu -> 0 <= dt -> (оценка связи числом M на модах < K) -> 2 * dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 -> 4 * dt * (M * M) * (Kq * Kq * Kq) * inject_Z (Z.of_nat (K * K)) * modal_energy K a0 <= nu -> energy_decreasing K (gtraj nu B K dt a0) /¤ enstrophy_decreasing K (gtraj nu B K dt a0) /¤ (forall n, энергия и энстрофия шага n не больше начальных) (GalerkinEnstrophyRegion.v:384) — обе посылки full_regularity_2d (EnergyEstimate.v:201) доказаны для траектории. ') + CL + '.';
const N_STR = 'Definition stretch (B : nat -> nat -> nat -> Q) (K : nat) (a : nat -> Q) : Q := sum_Q_ns (fun k => wgt k * a k * nl B K a k) K (GalerkinEnstrophyRegion.v:101) — вклад нелинейного члена в скорость энстрофии.';
const N_ERATE = 'galerkin_enstrophy_rate : forall nu B K (a : nat -> Q), sum_Q_ns (fun k => wgt k * a k * grhs nu B K a k) K == - (2) * nu * Vorticity.palinstrophy K a + stretch B K a (GalerkinEnstrophyRegion.v:105); тождество шага — galerkin_step_enstrophy (:155). ' + CL + '.';
const N_BTRI = 'Definition Btri (GalerkinEnstrophyRegion.v:198) — триада на модах 0, 1, 2: da_0 = −5 a_1 a_2, da_1 = 8 a_0 a_2, da_2 = −3 a_0 a_1 (Btri_nl, :206); сохраняет энергию (Btri_energy_conserving, :214), вытяжения нет (Btri_no_stretching, :220), |Btri| <= 8 (Btri_bound, :227).';
const N_TRI = L('triad_traj_regular : forall nu dt (a0 : modal_state), 0 <= nu -> 0 <= dt -> 2 * dt * nu * 9 <= 1 -> 4 * dt * (8 * 8) * (3 * 3 * 3) * 9 * modal_energy 3 a0 <= nu -> forall n, energy_at 3 (gtraj nu Btri 3 dt a0) n <= energy_at 3 (gtraj nu Btri 3 dt a0) 0 /¤ enstrophy_at 3 (gtraj nu Btri 3 dt a0) n <= enstrophy_at 3 (gtraj nu Btri 3 dt a0) 0 (GalerkinEnstrophyRegion.v:437). ') + CL + '.';
const N_PSV = L('pair_stretching_values : stretch (adv T_pair) 2 a_unit == - (3) /¤ stretch (adv T_pair) 2 a_pm == 3 (GalerkinEnstrophyRegion.v:191); a_pm (:189) — состояние (1, −1). ') + CL + '.';
const N_S2D = 'stretching_2d_is_literal_zero : Vorticity.stretching_2d = 0 (GalerkinEnstrophyRegion.v:96; доказательство — reflexivity). Definition stretching_2d : Q := 0 (Vorticity.v:189); Theorem unconditional_2d : stretching_2d == 0 (AttackSynthesis.v:293). Понятия размерности в каталоге нет. ' + CL + '.';
const N_RSTEP = 'region_invariant_step : forall (nsc : NSCoupling) nu dt K (Nl : modal_state -> nat -> Q) (a : modal_state), 0 < nu -> 0 <= dt -> dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 -> (forall k, (1 <= k)%nat -> (k <= K)%nat -> Qabs (Nl a k) <= boundary_damping nu k) -> in_region nu K a -> in_region nu K (gstep_gen nu dt Nl a) (GalerkinEnstrophyRegion.v:470); gstep_gen (:457) — шаг Эйлера с произвольным нелинейным членом в нумерации InvariantRegion.v (моды k = 1..K, затухание nu k^2). ' + CL + '.';
const N_RITER = 'region_invariant_iter : forall (nsc : NSCoupling) nu dt K Nl (a0 : modal_state), 0 < nu -> 0 <= dt -> dt * nu * inject_Z (Z.of_nat (K * K)) <= 1 -> (forall b, in_region nu K b -> forall k, (1 <= k)%nat -> (k <= K)%nat -> Qabs (Nl b k) <= boundary_damping nu k) -> in_region nu K a0 -> forall n, in_region nu K (giter nu dt Nl a0 n) (GalerkinEnstrophyRegion.v:517); giter (:461) — траектория шага gstep_gen. Для нелинейного члена с B_coeff условие выполнено тривиально (formal_region_invariant, :564). ' + CL + '.';
const N_RME = 'region_iter_mode_enstrophy (GalerkinEnstrophyRegion.v:535): при посылках region_invariant_iter inject_Z (Z.of_nat (k * k)) * a_k^2 <= A_inv nu * A_inv nu на всей траектории, при 1 <= k <= K. Сумма вкладов мод при этом растёт с K: оценки энстрофии, равномерной по K, область не даёт. ' + CL + '.';
const N_INR = 'Definition in_region (nu : Q) (K : nat) (a : modal_state) : Prop := forall k, (1 <= k)%nat -> (k <= K)%nat -> Qabs (a k) <= A_inv nu / inject_Z (Z.of_nat k) (InvariantRegion.v:65); A_inv nu := nu / C_B (:38); boundary_damping nu k := nu * k * A_inv nu (:196).';
const N_FNB = L('forcing_in_region_not_a_bound : @forcing_in_region ex_coupling 1 1 == 0 /¤ @mode_forcing ex_coupling 1 3 a_ex == 1 (GalerkinEnstrophyRegion.v:626); ex_coupling (:604) — экземпляр записи NSCoupling без правила отбора триад; состояние a_ex (:609) лежит в области (a_ex_in_region, :616). ') + CL + '.';
const N_CRT = 'Theorem conditional_regularity_theorem (ConcentrationBound.v:232) — три свойства выражения per_mode_amplitude nu E0 k := 2 * C_B * E0 / (nu * k): положительность, неотрицательность взвешенного квадрата, монотонность по k. Состояний, области и условия в ней нет. ' + CL + '.';
const N_FB = 'Theorem forcing_bound (TriadicInteraction.v:307) и Lemma B_coeff_bounded (:126) — в числе пяти объявлений, использующих поле B_raw_antisym_bounded (все в TriadicInteraction.v); теоремы о регулярности от этого поля не зависят. ' + CL + '.';

// ================================================================ глава IX.5
{
  const { fix, add, save } = open('part09-ch05');
  const C24 = 'Во-первых, опорный НС-кластер ToS — большой формальный слой, и он *условен*: часть его теорем берёт посылками положительность константы связи и оценку связи нелинейного члена (запись посылок `NSCoupling`: `C_B_positive`, `B_raw_antisym_bounded`), прежние оценки по времени — посылки об убывании энергии и энстрофии; с ноября 2026 года это посылки теорем, а не аксиомы проекта.';
  const C31A = '*Без условий на начальные данные* (при условии на шаг схемы): энергия не растёт и ограничена начальной;';
  const C31B = 'для связей без вытяжения то же верно для энстрофии — это формальный образ двумерного случая.';
  const C31C = '*Условно* (если нелинейный член в инвариантной области не превосходит затухания на её границе): траектория остаётся в области — формальный образ трёхмерной регулярности.[^1]';
  const C86 = L('Поэтому энергия *не растёт* и ограничена начальной, $E(n)¤le E(0)$, — при всяком начальном состоянии, без условий на данные; условие стоит только на шаг схемы, и оно известно заранее.[^3]');
  const C103 = 'Поэтому энстрофия остаётся под контролем. В формальном галёркинском (модальном) слое вытяжение — это вклад нелинейного члена в скорость энстрофии, и доказано: для связи без вытяжения энстрофия, как и энергия, не растёт на всей траектории — при всяком начальном состоянии, при условии на шаг схемы.';
  const C103B = 'Размерности в формализации нет: связь без вытяжения — формальный образ двумерного случая.[^4]';
  const C108 = L('В том же модальном слое регулярность доказана *условно*: если начальное состояние лежит в инвариантной области (амплитуды мод малы относительно $¤nu$), а нелинейный член в этой области не превосходит затухания на её границе, то при малом шаге схемы вся траектория остаётся в области; но что эта оценка нелинейного члена выполнена для связи с вытяжением, не доказано.[^5]');
  const C116 = 'ToS не претендует на её решение — он формализует, *что именно* доказуемо (диссипация, регулярность для связей без вытяжения, условная — для связей с вытяжением) и *где* проходит граница.';
  const F1A = L('Опорный кластер — каталог `navier_stokes/` Rocq-репозитория ToS. Оценки на траектории схемы: `galerkin_traj_energy_apriori` (`GalerkinEnergyEstimate.v`: $E(n)¤le E(0)$ при условии на шаг),');
  const F1B = '`no_stretching_traj_apriori` (`GalerkinEnstrophyRegion.v`: без вытяжения не растут ни энергия, ни энстрофия),';
  const F1C = '`region_invariant_iter` (`GalerkinEnstrophyRegion.v`: траектория остаётся в инвариантной области, если нелинейный член в ней не превосходит граничного затухания);';
  const F1D = '`millennium_gap_precise` (`AttackSynthesis.v`, точная формулировка открытого зазора).';
  const F1E = '*Посылки:* теоремы прежних файлов, в которые входит константа связи, получают аргументом запись `NSCoupling` (`GalerkinSystem.v`) — константу связи с её положительностью (`C_B_positive`) и оценку связи `B_raw_antisym_bounded`';
  const F1F = '(в `TriadicInteraction.v` она же — лемма `B_coeff_bounded`; на неё опирается оценка суммарного воздействия на моду, `forcing_bound`).';
  const F1G = 'Прежние оценки по времени — `energy_bounded_by_initial`, `regularity_3d_small_data` (`EnergyEstimate.v`) — записи не берут и условны по своим посылкам об убывании (`energy_decreasing`, `conditionally_regular`).';
  const F1H = 'Объявлений-аксиом кластер не делает.';
  const F3C = L('Оценка на траектории — `galerkin_traj_energy_apriori` (`GalerkinEnergyEstimate.v`): для ограниченной связи, сохраняющей энергию, при $2¤Delta t¤,¤nu K^2¤le1$ и $4¤Delta t¤,M^2K^3E(0)¤le¤nu$ ($K$ — число мод, $M$ — граница связи) энергия не растёт от шага к шагу при всяком начальном состоянии.');
  const F3D = 'Без условия на шаг явная схема энергию может увеличить (`galerkin_euler_energy_can_grow`).';
  const F3E = 'Прежние `energy_bounded_by_initial`, `energy_monotone` (`EnergyEstimate.v`) дают ту же оценку для произвольной последовательности состояний при посылке `energy_decreasing`; без посылки она неверна (`energy_bound_needs_premise`).';
  const F3F = L('Для системы с `B_coeff` посылка доказана при $¤Delta t¤,¤nu K^2¤le1$ (`formal_traj_energy_decreasing`). 0 аксиом.');
  const F4A = '`no_stretching_traj_apriori` (`GalerkinEnstrophyRegion.v`): вытяжение — вклад нелинейного члена в скорость энстрофии (`stretch`, `galerkin_enstrophy_rate`); для ограниченной связи, сохраняющей энергию и не имеющей вытяжения, при условии на шаг энергия и энстрофия не растут на всей траектории.';
  const F4B = 'Пример такой связи с ненулевым переносом — триада `Btri` (`triad_traj_regular`); у связи с вытяжением нелинейный член энстрофию производит (`pair_stretching_values`).';
  const F4C = 'Размерности в формализации нет: `unconditional_2d` (`AttackSynthesis.v`) есть равенство `stretching_2d == 0` для постоянной, заданной нулём (`stretching_2d_is_literal_zero`). 0 аксиом.';
  const F5A = L('`region_invariant_iter` (`GalerkinEnstrophyRegion.v`): область — покомпонентные оценки $¤lvert a_k¤rvert¤le A/k$, $A=¤nu/C_B$ (`in_region`, `InvariantRegion.v`); если в области $¤lvert N_k¤rvert¤le¤nu kA$ и $¤Delta t¤,¤nu K^2¤le1$, шаг схемы область сохраняет (`region_invariant_step`), и вклад каждой моды в энстрофию не превосходит $A^2$ на всей траектории (`region_iter_mode_enstrophy`).');
  const F5B = 'Что условие на нелинейный член выполнено для связи с вытяжением, не доказано — это и есть зазор; из записи посылок оно не следует (`forcing_in_region_not_a_bound`).';
  const F5C = L('Прежние теоремы: `conditional_regularity_theorem` (`ConcentrationBound.v`) — три свойства формулы $2C_BE_0/(¤nu k)$; `regularity_3d_small_data` (`EnergyEstimate.v`) — индукция по посылке `conditionally_regular`. 0 аксиом.');

  // место 5.7 (стр. 24)
  fix('Во-первых, опорный НС-кластер ToS — большой формальный слой, и он *условен*: его теоремы', 'NSCoupling', { claim: C24,
    note: DONE + ': названо, что записью посылок пользуется часть теорем, а прежние оценки по времени условны по своим посылкам. Запись получают аргументом 318 теорем каталога из 881 (первая вычитка); energy_bounded_by_initial, regularity_3d_small_data, unconditional_2d её не получают.' });
  add({ theorem: 'energy_decreasing', file: EE, claim: C24, note: '«Посылки об убывании энергии и энстрофии»: ' + N_ED + ' ' + N_CR });
  fix('Во-вторых, трёхмерная регулярность доказана лишь *условно*;', 'regularity_3d_small_data', { theorem: 'region_invariant_iter', file: ER, assumptions: CL,
    note: KEPT + 'условная теорема о траектории теперь есть: ' + N_RITER });

  // места 5.4–5.6 (стр. 31–34)
  fix('*Безусловно*: энергия диссипирует и ограничена начальной;', 'energy_bounded_by_initial', { claim: C31A, theorem: 'galerkin_traj_energy_apriori', file: GE, assumptions: CL,
    note: DONE + ': оценка названа так, как она доказана. ' + N_APR });
  fix('двумерное течение регулярно (нет вытяжения вихря).', 'unconditional_2d', { claim: C31B, theorem: 'no_stretching_traj_apriori', file: ER, assumptions: CL,
    note: DONE + ' (развилка 2, вариант 1). ' + N_NS });
  fix('*Условно* (в инвариантной области, при докритической', 'conditional_regularity_theorem', { claim: C31C, theorem: 'region_invariant_iter', file: ER, assumptions: CL,
    note: DONE + ' (развилка 3, вариант 1). ' + N_RITER });

  // место 5.4 (стр. 86–87)
  fix('Поэтому энергия *монотонно убывает*', 'energy_monotone', { claim: C86, theorem: 'galerkin_traj_energy_apriori', file: GE, assumptions: CL,
    note: DONE + ': «безусловный результат» заменён доказанным — при всяком начальном состоянии, при условии на шаг. ' + N_APR + ' Без условия на шаг оценка неверна: galerkin_euler_energy_can_grow (:165).' });

  // место 5.5 (стр. 103–104; развилка 2, вариант 1)
  fix('Поэтому энстрофия остаётся под контролем, и в формальном галёркинском', 'unconditional_2d', { claim: C103, theorem: 'no_stretching_traj_apriori', file: ER, assumptions: CL,
    note: DONE + ' (развилка 2, вариант 1). ' + N_NS });
  add({ theorem: 'stretch', file: ER, claim: C103, note: '«Вытяжение — это вклад нелинейного члена в скорость энстрофии»: ' + N_STR + ' ' + N_ERATE });
  add({ theorem: null, file: ER, claim: C103B,
    note: DONE + ' (развилка 2, вариант 1). Верно: понятия размерности, завихренности как поля и коэффициентов действительной адвекции в каталоге нет; ' + N_S2D });

  // место 5.6 (стр. 108–110; развилка 3, вариант 1)
  fix('В том же модальном слое регулярность доказана *условно* — если поле остаётся', 'regularity_3d_small_data', { claim: C108, theorem: 'region_invariant_iter', file: ER, assumptions: CL,
    note: DONE + ' (развилка 3, вариант 1). ' + N_RITER });
  add({ theorem: 'forcing_in_region_not_a_bound', file: ER, assumptions: CL, claim: C108,
    note: '«Что эта оценка выполнена для связи с вытяжением, не доказано» — из записи посылок она не следует: ' + N_FNB });

  // стр. 117
  fix('ToS не претендует на её решение — он формализует, *что именно* доказуемо (диссипация, двумерная', null, { claim: C116,
    note: DONE + ': перечень приведён к доказанному — galerkin_traj_energy_apriori (GalerkinEnergyEstimate.v:444), no_stretching_traj_apriori (GalerkinEnstrophyRegion.v:384), region_invariant_iter (:517).' });

  // сноска 1
  fix('Опорный кластер — каталог `navier_stokes/` Rocq-репозитория ToS: `energy_bounded_by_initial`', 'energy_bounded_by_initial', { claim: F1A, theorem: 'galerkin_traj_energy_apriori', file: GE, assumptions: CL,
    note: DONE + ': сноска переписана. ' + N_APR });
  fix('`unconditional_2d` (`AttackSynthesis.v`, двумерное вытяжение нулевое)', 'unconditional_2d', { claim: F1B, theorem: 'no_stretching_traj_apriori', file: ER, assumptions: CL,
    note: DONE + ' (развилка 2, вариант 1). ' + N_NS });
  fix('`conditional_regularity_theorem` (трёхмерная регулярность при условии)', 'conditional_regularity_theorem', { claim: F1C, theorem: 'region_invariant_iter', file: ER, assumptions: CL,
    note: DONE + ' (развилка 3, вариант 1). ' + N_RITER });
  fix('`millennium_gap_precise` (точная формулировка открытого зазора)', 'millennium_gap_precise', { claim: F1D, verdict: 'mismatch-statement' });
  fix('*Посылки:* теоремы кластера получают аргументом запись', 'B_raw_antisym_bounded', { claim: F1E,
    note: DONE + ': слова «на которой держится условность трёхмерной регулярности» сняты. Поле B_raw_antisym_bounded используют пять объявлений TriadicInteraction.v; теоремы о регулярности от него не зависят.' });
  fix('(в `TriadicInteraction.v` она же — лемма `B_coeff_bounded`).', 'B_coeff_bounded', { claim: F1F, assumptions: CL,
    note: DONE + ': названо, что на оценку опирается. ' + N_FB });
  add({ theorem: 'forcing_bound', file: TI, assumptions: CL, claim: F1F, note: N_FB });
  add({ theorem: 'energy_bounded_by_initial', file: EE, assumptions: CL, claim: F1G, note: DONE + ': новая фраза. ' + N_EBI });
  add({ theorem: 'regularity_3d_small_data', file: EE, assumptions: CL, claim: F1G, note: N_R3D });
  add({ theorem: 'energy_decreasing', file: EE, claim: F1G, note: N_ED });
  add({ theorem: 'conditionally_regular', file: EE, claim: F1G, note: N_CR });
  fix('Объявлений-аксиом кластер не делает; в отличие', 'NSCoupling', { claim: F1H,
    note: DONE + ': слова об условности по записи посылок сняты (они перенесены в предыдущие фразы сноски). Строк Axiom и Parameter в каталоге navier_stokes нет; запись NSCoupling — класс (GalerkinSystem.v:216).' });

  // сноска 3: вторая половина (место 5.4)
  fix('Далее — `energy_bounded_by_initial`, `energy_monotone` (`EnergyEstimate.v`): $E$ монотонна и ограничена начальной, безусловно. Опираются', 'energy_bounded_by_initial', { claim: F3C, theorem: 'galerkin_traj_energy_apriori', file: GE, assumptions: CL,
    note: DONE + ': вторая половина сноски. ' + N_APR });
  add({ theorem: 'galerkin_euler_energy_can_grow', file: GE, assumptions: CL, claim: F3D, note: N_GROW });
  fix('Далее — `energy_bounded_by_initial`, `energy_monotone` (`EnergyEstimate.v`): $E$ монотонна и ограничена начальной, безусловно.', 'energy_monotone', { claim: F3E, assumptions: CL,
    note: DONE + ': названа посылка прежних теорем. ' + N_EBI });
  add({ theorem: 'energy_bounded_by_initial', file: EE, assumptions: CL, claim: F3E, note: N_EBI });
  add({ theorem: 'energy_decreasing', file: EE, claim: F3E, note: N_ED });
  add({ theorem: 'energy_bound_needs_premise', file: GE, assumptions: CL, claim: F3E, note: N_PREM });
  add({ theorem: 'formal_traj_energy_decreasing', file: GE, assumptions: CL, claim: F3F, page_price: '0 аксиом', note: N_FORM });

  // сноска 4 (место 5.5; развилка 2, вариант 1)
  fix('`unconditional_2d`: `stretching_2d == 0` (`AttackSynthesis.v`). Отсутствие вытяжения', 'unconditional_2d', { claim: F4A, theorem: 'no_stretching_traj_apriori', file: ER, assumptions: CL,
    note: DONE + ' (развилка 2, вариант 1): сноска переписана. ' + N_NS });
  add({ theorem: 'stretch', file: ER, claim: F4A, note: N_STR });
  add({ theorem: 'galerkin_enstrophy_rate', file: ER, assumptions: CL, claim: F4A, note: N_ERATE });
  add({ theorem: 'Btri', file: ER, claim: F4B, note: N_BTRI });
  add({ theorem: 'triad_traj_regular', file: ER, assumptions: CL, claim: F4B, note: N_TRI });
  add({ theorem: 'pair_stretching_values', file: ER, assumptions: CL, claim: F4B, note: N_PSV });
  add({ theorem: 'unconditional_2d', file: AS, assumptions: CL, claim: F4C, page_price: '0 аксиом', note: N_S2D });
  add({ theorem: 'stretching_2d', file: VO, claim: F4C, note: 'Definition stretching_2d : Q := 0 (Vorticity.v:189).' });
  add({ theorem: 'stretching_2d_is_literal_zero', file: ER, assumptions: CL, claim: F4C, page_price: '0 аксиом', note: N_S2D });

  // сноска 5 (место 5.6; развилка 3, вариант 1)
  fix('`conditional_regularity_theorem` и инвариантная область', 'conditional_regularity_theorem', { claim: F5A, theorem: 'region_invariant_iter', file: ER, assumptions: CL,
    note: DONE + ' (развилка 3, вариант 1): сноска переписана. ' + N_RITER });
  add({ theorem: 'in_region', file: IR, claim: F5A, note: N_INR });
  add({ theorem: 'region_invariant_step', file: ER, assumptions: CL, claim: F5A, note: N_RSTEP });
  add({ theorem: 'region_iter_mode_enstrophy', file: ER, assumptions: CL, claim: F5A, note: N_RME });
  add({ theorem: 'forcing_in_region_not_a_bound', file: ER, assumptions: CL, claim: F5B, note: N_FNB });
  add({ theorem: 'conditional_regularity_theorem', file: CB, assumptions: CL, claim: F5C, page_price: '0 аксиом', note: N_CRT });
  add({ theorem: 'regularity_3d_small_data', file: EE, assumptions: CL, claim: F5C, page_price: '0 аксиом', note: N_R3D });
  add({ theorem: 'conditionally_regular', file: EE, claim: F5C, note: N_CR });

  save();
}
