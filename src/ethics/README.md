# src/ethics/ — Формализация ветки Этики (план)

Coq-формализация ветки Этики (прозаический свод: `Книги/Этика/00 Этика — рабочая запись.md`,
записи Р-1…Р-83). Конвенции проекта: **0 новых аксиом** (строим на готовом ядре), **всё `Qed`**,
E/R/R-заголовок в каждом файле, `From ToS Require Import …`.

---

## ⚠ СТЕНА ЧЕСТНОСТИ (что формализуем, а что — НЕТ)

Coq кодирует **логическую СТРУКТУРУ** ветки, НЕ ценностные суждения. Мы **не доказываем**
«добро есть благо» — это не теорема Coq. Формализуемо и честно:

- **decidable отношения / классификации** — статус соответствия, виды ответственности, критерий зла;
- **ортогональности** — вид ⊥ магнитуда, техника ⊥ воля (два независимых параметра);
- **демаркации как предикаты** — «полярность включается ⟺ порядок на кону»;
- **процессы-динамики** — спираль + условие выхода (признание); путь = заполнение;
- **структурные тождества-как-определения** — порядок := well-formed; правильно := соответствие.

НЕ формализуем (остаётся прозой + честный флаг): что порядок «хорош», что намерение-на-правду
«должно». Каждый файл несёт `(* ЧЕСТНОСТЬ: формализована структура X; ценностная интерпретация —
в прозе Р-NN, не в Qed *)`.

Связь с правилом проекта [[untangle-overbranding-structurally]] / [[err-razbor-each-new-thread]]:
форсированное-условное + честный wall, без оверклейма.

---

## Планируемые файлы (первая волна)

| файл | формализует (структура) | якоря Р |
|---|---|---|
| ✅ `EthicsStatus.v` **(15 Qed, 0 ax)** | правильно = СООТВЕТСТВИЕ (decidable status подходит/не-подходит); ось: (a) ЗДО-гейт кандидатов + (b) отбор (argmax / мин-отклонение, anti-overqualified); множественно-правильное = ничья | Р-46/50/76 |
| ✅ `EthicsModality.v` **(14 Qed, 0 ax)** | резкое ядро (двузначность + `no_neutral_third` КОНСТРУКТИВНО); демаркация (`engaged ⟺ at_stake`; незадействование ≠ третье значение); вид ⊥ магнитуда (`intent/magn_does_not_fix_*`) | Р-42/53/54 |
| ✅ `EthicsEvil.v` **(11 Qed, 0 ax)** | критерий зла = не-правда-ВИД (не магнитуда); реляционно (`internal_not_punishable`, нужен 2-й затронутый); положительно-реально-но-несоответственно (`illusion_not_empty` ∧ `illusion_not_corresponds`); инструментально (`no_radical_motive`) | Р-59/79/80 |
| ✅ `EthicsResponsibility.v` **(11 Qed, 0 ax)** | 3 условия (`forced_not_responsible`, `not_at_stake_not_responsible`); возмещение←вред / наказание←вина (`honest_harm_…`, `evil_harm_both`); признание (`acknowledgment_cancels_punishment` / `…keeps_restitution`); честное-незнание (`honest_ignorance_no_duty`); степень-по-свободе | Р-56/57/58/62/72 |
| ✅ `EthicsPathWisdom.v` **(12 Qed, 0 ax)** | путь = заполнение, техника ⊥ воля (`tech_does_not_fix_will`); мудрость = единство (`sophist_not_wise`, `low_tech_not_wise`, `wise_needs_both`); спираль (`spiral_deepens`) + выход (`acknowledgment_exits`); восстановление (`recovery_always_possible`, `acknowledgment_keeps_depth`) | Р-65/69/70 |
| ✅ `EthicsCapstone.v` **(8 Qed, 0 ax)** | сборка 7 несущих осей (`axis1`…`axis7` + `capstone_spine`); ось 5 (логика-показывает-не-навязывает) честно = ПРОЗА (вне решаемой модели); `Print Assumptions` = 0 аксиом по всей ветке | Р-83 |

(Н-7 справедливость и Н-2 эпистемология — в первой волне сворачиваются в Capstone или пропускаются;
проверить пересечения с существующими src.)

---

## Конвенции / сборка

- **E/R/R заголовок** в каждом файле (Elements/Roles/Rules/Status + `STATUS: N Qed, 0 Admitted, 0 axioms`).
- **Импорты:** `From ToS Require Import foundation.Distinction` (L2/L3, classic), `foundation.RoleLimitSpecies`
  (regular/singular = путь сходящийся/спираль), и т. д. Реплицировать малое локально при stale .vo
  (`(* Replicated from X.v *)`).
- **`-Q src ToS`** уже покрывает `src/ethics/` ⇒ новый `-Q` НЕ нужен; только **APPEND** строк файлов
  в `_CoqProject` (LOST-UPDATE hotspot — только дописывать; `tools/check_coqproject.ps1` перед коммитом).
- **Сборка (Windows):** реальный coqc — `C:\Programs\…` (см. [[rocq-build-windows]]); компилировать
  по одному файлу, считать `Qed`, затем `make`.
- **Порядок:** Status → Modality → Evil → Responsibility → PathWisdom → Capstone (каждый на предыдущих).

---

## Статус

Файл 1/6 `EthicsStatus.v` ✅ ГОТОВ (2026-06-20): 15 Qed, 0 Admitted, 0 axioms (Print Assumptions:
Closed under the global context); добавлен в `_CoqProject`. Воля-ветка (`Книги/Воля/`) — отдельно,
отложена к метафизике; её связь с этикой зафиксирована (ВЛ-1), в первую волну НЕ входит.
**ПЕРВАЯ ВОЛНА ЗАВЕРШЕНА (2026-06-20).** Все 6 файлов ✅: `EthicsStatus` (15) · `EthicsModality` (14) ·
`EthicsEvil` (11) · `EthicsResponsibility` (11) · `EthicsPathWisdom` (12) · `EthicsCapstone` (8) =
**71 Qed, 0 Admitted, 0 axioms** (Print Assumptions: Closed под global context по всей ветке).
Зарегистрированы в `_CoqProject` (в порядке зависимостей).

**ВТОРАЯ ВОЛНА — мост к ИИ:** ✅ `EthicsAI.v` **(7 Qed, 0 ax)** ГОТОВ (2026-06-20). Оператор-нейтрально
(ИИ = §X-оператор); **техника-безопасность ≠ alignment** (`tech_safe_not_imply_aligned`,
`deceptive_yet_correct_exists` — софист-ИИ: passes typecheck, но воля=не-правда ⇒ ось техники
[≈ AIInterface/AI_FallacyDetector] НЕ покрывает ось воли, которую добавляет этика); ответственность-шарнир
(`not_free_ai_not_punishable` — не свободен → перенос к создателям; `honest_ai_not_punishable`);
`ai_wisdom_needs_both`. ЧЕСТНО: шарнир «есть ли у ИИ воля» открыт (воля-ветка); операц. моста нет.
**ВСЕГО src/ethics/ = 7 файлов, 78 Qed, 0 axioms.**
Ещё открыто: паркованное (виды-зла, восстановление-детали, типология добродетелей); ось 5 — проза.

**ТРЕТЬЯ ВОЛНА — углубление полярности умысла + истинный порядок (2026-07-16, Р-106…Р-117):**
✅ `EthicsIntentDeep.v` **(16 Qed, 0 ax)** — углублённый критерий (Ш-58…Ш-64 сводного прохода):
матрица «воля Другого × чей интерес» (полюса на диагонали, `evil_good_exclusive`; патернализм и
обмен вне полярности); без умысла нет зла (`no_intent_no_evil` — лев-пример); клетка добра
расщеплена притяжением (`attraction_blocks_good`, `merely_correct_not_good`); вид-удовольствие
только у зла (`good_no_pleasure_motive` + `sadistic_evil_exists` — асимметрия полюсов, Р-112);
тест получателя = L2-неуниверсализуемость (`evil_fails_receiver_test`); решаемость полюсов
(`evil_b_reflect`, `good_b_reflect`); проверка по адресату и времени (`rationalization_dishonest`,
`genuine_anti_trouble_exists`). ЧЕСТНО: булева структура; добрая натура/наблюдатель-градуальность —
проза. ✅ `EthicsTrueOrder.v` **(9 Qed, 0 ax)** — истинный порядок (Р-110/Р-113): башня объемлющих
уровней; `true_implies_local` + мафия-контрпример (`mafia_locally_optimal` ∧ `mafia_not_true_order`);
`breaks_above_not_true`; мера решаема конечной проверкой (`true_order_b_reflect` — регресс конечен);
вершина в мере (`apex_checked`); единственность не следует (`true_order_not_unique` — пул
равно-наилучших, открытый хвост Р-113 честно). Print Assumptions: Closed по обоим файлам.
**ВСЕГО src/ethics/ = 9 файлов, 103 Qed, 0 Admitted, 0 axioms.** Зарегистрированы в `_CoqProject`
(check_coqproject: OK). Осталось из реестра ⊢нов: нов-1..3 (EthicsERRBridge), нов-4 (EthicsJustice),
нов-5 (EthicsRuleHierarchy); согласование старого `EthicsEvil.is_evil` (вид-не-правда) с углублённым
критерием — мостовая лемма, кандидат следующей волны.

**ЧЕТВЁРТАЯ ВОЛНА — эгоизм (2026-07-24, Р-119…Р-121, хвост ветки эго):**
✅ `EthicsEgoism.v` **(19 Qed, 0 ax, Closed)** — эгоизм = УСТАНОВКА (хроника центров nat→Center;
`egoism_births_acts`, `act_is_not_stance`); ориентация оси матрицы умысла, не клетка
(`orientation_alone_not_evil`, `evil_needs_both`); граница с заботой = центр, не выгодополучатель
(`boundary_is_center_not_beneficiary`); служение записи, которая не волит (`egoism_serves_record`,
`record_returns_no_will`); третий центр рушит пару эгоизм/альтруизм (`antipode_is_truth_not_altruism`);
несправедливость назначения по зоне (`egoist_assignment_unjust`); застывшая запись расходится с
движущейся истиной неограниченно (`frozen_misses_unboundedly`, `egoism_breeds_illusion`).
Капстоун `egoism_canon`. ЧЕСТНО: булевы тени; ценностный слой — проза.
**ВСЕГО src/ethics/ = 10 файлов, 122 Qed, 0 Admitted, 0 axioms.**
