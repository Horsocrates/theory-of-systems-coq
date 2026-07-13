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
