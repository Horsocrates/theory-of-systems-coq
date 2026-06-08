# Database - cluster `arch_of_reasoning`

_Generated from `arch_of_reasoning.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**6 files / 117 Qed.** Score distribution: s5=0 / s4=0 / s3=2 / s2=4 / s1=0 / s0=0

---

## #1 - `Architecture_of_Reasoning/AI_FallacyDetector.v` - score 2 (methods)

**AI fallacy/hallucination detector over ERR: an extractable verifier**

- **Topic.** A reasoning verifier checking domain coverage, self-reference and named fallacies (ad hominem, straw man, false dilemma, ...); an LLM-response analyzer; hallucination types mapped to architecture violations with a severity scale; CoT templates; a safety check; quality thresholds; and extractable wrappers for all of it.
- **Role.** Applied/extractable layer of the reasoning architecture (consumes Architecture_of_Reasoning.v). Self-contained. Vein-E adjacent (fallacy = ERR violation).
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** ToS_Arch: Architecture_of_Reasoning (local)
- **E/R/R.** _Elements:_ шаги рассуждения; сигналы ответа LLM; типы галлюцинаций. _Roles:_ детектор = роль-верификатор; домены/самоссылка как роли-проверки. _Rules:_ valid_requires_all_domains; safety_blocks_ad_hominem; hallucinations_are_violations. _P4:_ конечная проверяемая процедура (Element, извлекается в OCaml); ошибка = нарушение ERR/архитектуры, не отдельная сущность.
- **Classical counterpart.** Fallacy catalogues, hallucination taxonomies and CoT-validation are known in informal logic / AI-safety; NEW is the EXTRACTABLE Coq detector that maps named fallacies AND hallucinations onto ERR/architecture violations and enforces 'valid requires all domains'.
- **Tags.** reasoning, fallacy-detector, hallucination, extractable, vein-E, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `Domain/FailureMode/LevelConfusion/ReasoningStep/ReasoningAttempt/VerificationResult/is_valid` | Definition | типы домена, шага, результата |
| `verify_reasoning/detect_ad_hominem/_straw_man/_false_dilemma/_appeal_to_tradition/_false_analogy/_non_sequitur/_hasty_generalization/_confirmation_bias` | Definition | детекторы именованных ошибок |
| `valid_requires_all_domains/safety_blocks_ad_hominem/cot_template_complete` | Theorem | ★ валидность требует всех доменов |
| `HallucinationType/hallucination_to_violation/hallucinations_are_violations/hallucination_severity_to_violation/severe_hallucination_is_violation` | Definition/Theorem | ★ галлюцинации = нарушения архитектуры |
| `detector_catches_bias/_self_reference/valid_passes_detection/incomplete_detected/full_reasoning_meets_threshold/incomplete_fails_threshold` | Theorem | детектор ловит смещение/самоссылку |
| `extractable_verify/_llm_verify/_safety/_fix_prompt/_cot/_analyze/_detect_hallucination/_domain_score/_quality_check/_system_prompt` | Definition | ★ извлекаемые обёртки (OCaml) |

**Key lemmas (deep):**

- **`hallucinations_are_violations`** - Галлюцинации LLM отображаются на нарушения ERR/архитектуры рассуждения (по степени тяжести) — единая диагностика, где «выдумка» = структурное нарушение, а не отдельный феномен. Применение вены E (ошибка/парадокс = нарушение уровней/ERR) к AI-safety. _(hallucination, ERR-violation, ai-safety, vein-E)_
- **`valid_requires_all_domains`** - Валидное рассуждение обязано покрыть все домены (иначе детектируется неполнота) + извлекаемость в OCaml делает это исполнимым верификатором. Содержательно: проверяемый детектор, а не каталог. _(domain-coverage, extractable, verifier)_

**Uniqueness - score 2 (methods).** Извлекаемый Coq-детектор ошибок и галлюцинаций LLM поверх ERR: именованные ошибки и галлюцинации как нарушения архитектуры, проверка покрытия доменов, экспорт в OCaml.
> _Caveat:_ Каталоги ошибок и таксономии галлюцинаций известны в неформальной логике/AI-safety; вклад — извлекаемая формальная привязка к ERR, не новая теория.

---

## #2 - `Architecture_of_Reasoning/Architecture_of_Reasoning.v` - score 3 (new-framing)

**The architecture of reasoning: laws, ERR, domains, paradoxes as one ordered system**

- **Topic.** Ordered laws L1..L5 (level_lt), a reasoning-error dimension, an ordered domain sequence (D1..D6) with transitivity, a hierarchical level with self-application invalid, the ERR triad always extractable, fallacy types per domain, paradox types as self-referential level confusion, a unified diagnosis with mutually-exclusive violations, and classical-paradox stats.
- **Role.** Spine of the reasoning architecture (the Coq layer of the 'Архитектура Размышления' book); every other file in this folder builds on it. Self-contained. Vein-E core.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ законы L1..L5; домены D1..D6; уровни; ERR-триада. _Roles:_ архитектура = упорядоченная система ролей; нарушение = роль-диагноз по измерению. _Rules:_ level_lt; self_application_invalid; err_always_extractable; violations_exclusive. _P4:_ конечная упорядоченная архитектура (Element); парадокс = самоприменение уровня (role-limit запрещён); каждая ошибка — одно нарушение по измерению.
- **Classical counterpart.** Logical laws, fallacy/paradox catalogues, level/type hierarchies (Russell/Tarski) and the ERR (Elements/Roles/Rules) triad are individually known; NEW is their UNIFICATION into one ordered architecture where every reasoning error is a single 'architecture violation' along one of a few dimensions.
- **Tags.** reasoning, architecture, ERR, level-hierarchy, vein-E, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `Law/law_index/law_lt/L1_most_fundamental/OrderDimension/ReasoningError/error_dimension` | Definition | законы L1..L5, измерение ошибки |
| `Domain/domain_index/domain_lt/_le/domain_order_transitive/valid_domain_sequence` | Definition/Theorem | ★ упорядоченные домены D1..D6, транзитивность |
| `HierarchicalLevel/level_index/level_lt/valid_application/self_application_invalid/L2_applies_to_L1/L3_applies_to_L2` | Definition/Theorem | ★ самоприменение уровня недопустимо |
| `Constitution/FunctionalSystem/extract_elements/_roles/_rules/err_always_extractable` | Definition/Theorem | ★ ERR-триада всегда извлекаема |
| `FallacyType/D1..D6_FailureMode/domain_fallacy_count/total_type2_fallacies/D1_D6_most_vulnerable/D4_least_vulnerable` | Definition/Theorem | ошибки по доменам |
| `ParadoxType/LevelConfusion/is_self_referential/Resolution/paradox_resolution/paradoxes_require_dissolution/ERR_Component/err_to_level` | Definition/Theorem | ★ парадокс = самоссылочная путаница уровней |
| `ArchitectureViolation/violation_dimension/unified_diagnosis/violations_exclusive/well_formed_chain/complete_chain/verify_reasoning/valid_requires_constitution/ClassicalParadox/Liar/Russell/.../formalization_stats/stats_correct` | Definition/Theorem | ★ единый диагноз, нарушения взаимоисключающи |

**Key lemmas (deep):**

- **`unified_diagnosis`** - Ядро вены E: ВСЯКАЯ ошибка рассуждения — это одно «нарушение архитектуры» по одному из немногих измерений (нарушения взаимоисключающи, violations_exclusive). Объединяет ошибки, парадоксы и путаницу уровней в единую упорядоченную диагностику, привязанную к ERR. Это наблюдение-синтез, а не новая логика. _(unified-diagnosis, architecture-violation, vein-E, synthesis)_
- **`self_application_invalid`** - Самоприменение уровня к самому себе недопустимо (L_n применяется только к L_{n-1}) — формальный механизм, блокирующий парадоксы самоссылки (ср. ParadoxDissolution, Soundness.russell_untypable). Один и тот же запрет, что и в ядре ToS. _(self-reference, level-hierarchy, paradox-block)_

**Uniqueness - score 3 (new-framing).** Единая упорядоченная архитектура рассуждения (законы L1..L5, домены D1..D6, ERR-триада, уровни): всякая ошибка = одно взаимоисключающее «нарушение архитектуры»; парадокс = самоссылочная путаница уровней. Книжный Coq-каркас, ядро вены E.
> _Caveat:_ Логические законы, каталоги ошибок/парадоксов и иерархии уровней (Рассел/Тарский) известны по отдельности; вклад — их объединение в одну упорядоченную ERR-привязанную диагностику, не новая логика.

---

## #3 - `Architecture_of_Reasoning/CompleteFallacyTaxonomy.v` - score 2 (methods)

**Complete fallacy taxonomy: 156 fallacies in 5 types, counts proven**

- **Topic.** Type-1 defective-question and manipulation fallacies (36), type-2 domain fallacies (105, 70% of all), type-3 sequence violations, type-4 syndromes (self-reinforcing, invisible to the afflicted), type-5 methods with validity conditions, and the proven grand total of 156.
- **Role.** Enumeration leaf of the reasoning architecture (the catalogue). Self-contained.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List
- **E/R/R.** _Elements:_ 5 типов ошибок (T1..T5); по-доменные списки. _Roles:_ тип ошибки = роль-категория; счётчики как роли-инварианты. _Rules:_ type1_is_36; type2_is_105; grand_total=156; type2_is_70_percent. _P4:_ конечная пересчитанная таксономия (Element); счётчики доказаны, не заявлены.
- **Classical counterpart.** Catalogues of informal fallacies are old (Aristotle onward); NEW only as an exhaustively-counted, type-partitioned Coq taxonomy (156 fallacies in 5 types) with the counts proven.
- **Tags.** reasoning, fallacy, taxonomy, exhaustive, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `T1A_DefectiveQuestion/T1B_Manipulation/ManipulationCategory/all_T1A/all_T1B/T1A_count/T1B_count/type1_total/type1_is_36` | Definition/Theorem | ★ тип-1 = 36 |
| `D1..D6_Fallacy/all_D1..all_D6/D1_count..D6_count/type2_total/type2_is_105` | Definition/Theorem | ★ тип-2 (доменные) = 105 |
| `T3_SequenceViolation/all_T3/T3_count/T4_Syndrome/SyndromeCategory/all_T4/T4_count/syndrome_pervades_domains/_self_reinforces/_invisible_to_afflicted` | Definition/Theorem | ★ синдромы самоусиливаются, невидимы носителю |
| `T5_Method/MethodCategory/method_valid_condition/all_T5/T5_count/FallacyType/total_type1..5/grand_total/complete_taxonomy_156/type_breakdown/type2_is_70_percent/D1_D6_most_fallacies/D4_most_constrained/manipulation_dominates_type1` | Definition/Theorem | ★ итог 156, разбивка |

**Key lemmas (deep):**

- **`complete_taxonomy_156`** - Полная таксономия с ДОКАЗАННЫМ итогом 156 ошибок в 5 типах (type1=36, type2=105, ...) — счётчики не заявлены, а проверены Coq. Type-4 синдромы «невидимы носителю и самоусиливаются» — содержательная категория. Это исчерпывающая энумерация, не новая логика. _(taxonomy, 156, exhaustive, counts-proven)_

**Uniqueness - score 2 (methods).** Полная Coq-таксономия ошибок: 156 в 5 типах с доказанными счётчиками (36/105/...), синдромы самоусиливаются и невидимы носителю.
> _Caveat:_ Каталоги ошибок известны со времён Аристотеля; вклад — исчерпывающая пересчитанная формализация, не новая теория ошибок.

---

## #4 - `Architecture_of_Reasoning/DomainViolations_Complete.v` - score 2 (methods)

**Domain violations complete: 105 fallacies mapped to ERR corruption**

- **Topic.** Six domains D1..D6, each with a failure mode and a fallacy list (total 105), the mapping from failure mode to the corrupted ERR component (D1 corrupts Elements, D2 Roles, D3/D5/D6 Rules), per-domain counts (D1/D6 largest, D4 smallest), and that each fallacy has a unique domain.
- **Role.** Enumeration leaf mapping fallacies to ERR (with ERR_Fallacies). Self-contained.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List
- **E/R/R.** _Elements:_ 6 доменов D1..D6; режимы отказа; компоненты ERR. _Roles:_ режим отказа домена = роль, повреждающая конкретный компонент ERR. _Rules:_ D1_corrupts_elements; D2_corrupts_roles; D3/D5/D6_corrupts_rules; total_is_105. _P4:_ конечная пересчитанная карта (Element); каждая ошибка повреждает один компонент ERR.
- **Classical counterpart.** Domain-specific reasoning failures are discussed informally; NEW only as a Coq enumeration (105 domain fallacies) where each domain's failure mode is mapped to which ERR component (Elements/Roles/Rules) it corrupts.
- **Tags.** reasoning, domain-violation, ERR, exhaustive, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `Domain/domain_index/D1..D6_FailureMode/FailureMode/failure_mode_domain/D1..D6_Fallacy/Fallacy` | Definition | домены, режимы отказа, ошибки |
| `d1..d6_failure_mode/fallacy_failure_mode/fallacy_domain/all_D1..all_D6/D1_count..D6_count/total_fallacies/total_is_105` | Definition/Theorem | ★ счётчики, итог 105 |
| `ERR_Component/failure_mode_primary_corruption/D1_corrupts_elements/D2_corrupts_roles/D3_corrupts_rules/D5_corrupts_rules/D6_corrupts_rules` | Theorem | ★ режим → повреждаемый компонент ERR |
| `domain_fallacy_count/D1_D6_largest/D4_smallest/fallacy_unique_domain/domain_failure_mode_consistent/failure_mode_corrupts_err` | Theorem | уникальность домена ошибки |

**Key lemmas (deep):**

- **`failure_mode_corrupts_err`** - Каждый режим отказа домена повреждает конкретный компонент ERR (D1→Elements, D2→Roles, D3/D5/D6→Rules) — содержательная привязка 105 ошибок к структурной триаде. Объясняет ошибки через одну онтологию (ERR), а не как разрозненный список. _(domain-violation, ERR-corruption, mapping)_

**Uniqueness - score 2 (methods).** 105 доменных ошибок над 6 доменами, каждая отображена на повреждаемый компонент ERR (Elements/Roles/Rules), счётчики доказаны.
> _Caveat:_ Доменные сбои рассуждения обсуждаются неформально; вклад — пересчитанная формальная карта ошибка→ERR, не новая теория.

---

## #5 - `Architecture_of_Reasoning/ERR_Fallacies.v` - score 2 (methods)

**ERR fallacies: named fallacies bound to constitution/level structure**

- **Topic.** Levels L2..L4 (well-founded order), constitution kinds, the ERR always extractable, ordered domains, reasoning chains (strictly increasing, well-formed, complete), type-1 violations (invalid constitution: appeal to force, the big lie), type-2 domain failure modes (a long named list), type-3 reversals, type-4 syndromes, type-5 context-valid methods, verification, and ERR no-self-containment.
- **Role.** The ERR-binding core of the fallacy layer (with DomainViolations). Self-contained.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ уровни L2..L4; конституции; цепочки рассуждения. _Roles:_ ошибка = роль-нарушение конституции/уровня; ERR без самосодержания. _Rules:_ type1 = invalid constitution; well_formed_no_reversal; err_no_self_containment. _P4:_ конечные цепочки со строго возрастающими уровнями (Element); ERR не содержит себя (role-limit запрещён) — блок самоссылки.
- **Classical counterpart.** Named fallacies (straw man, ad hominem, equivocation, post hoc, ...) and the type-1/type-2/type-3 distinction are known; NEW is binding each to the ERR/level structure: type-1 violations have an invalid constitution, well-formed reasoning has a constitution and no reversal, ERR has no self-containment.
- **Tags.** reasoning, fallacy, ERR, constitution, vein-E, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `Level/L2/L3/L4/level_lt/_depth/_lt_irrefl/_lt_trans/L1_lt_L2/L2_lt_L3/L1_lt_L3` | Definition/Lemma | вполне-обоснованный порядок уровней |
| `Constitution/Trivial.../FunctionalSystem/get_Elements/_Roles/_Rules/err_always_extractable` | Definition/Theorem | конституции, ERR извлекаема |
| `ReasoningChain/chain_domains/is_strictly_increasing/well_formed_chain/complete_chain/ConstitutionStatus/Type1_Violation/is_type1_violation/appeal_to_force/big_lie/big_lie_is_invalid` | Definition/Theorem | ★ тип-1 = недопустимая конституция |
| `FailureMode/Type2_Violation/straw_man/ad_hominem/cherry_picking/equivocation/false_dilemma/.../domain_failure_modes_complete` | Definition/Theorem | тип-2 именованные ошибки |
| `Type3_Violation/find_reversal/check_type3_reversal/rationalization/circular_reasoning/Type4_Syndrome/confirmation_bias/Type5_Method/appeal_to_tradition/_intuition/argument_from_silence/type5_resolution` | Definition/Theorem | разворот, синдром, контекстно-валидные методы |
| `VerificationResult/verify_step1_constitution/_step2_sequence/verify_reasoning/type1_blocks_reasoning/ViolationType/violation_to_type/types_exclusive/err_no_self_containment/well_formed_reasoning/_has_constitution/_no_reversal` | Theorem | ★ ERR без самосодержания; типы взаимоисключающи |

**Key lemmas (deep):**

- **`err_no_self_containment`** - ERR-структура не содержит саму себя — формальный запрет самоссылки на уровне триады, тот же механизм, что блокирует парадокс Рассела (ср. Soundness.russell_untypable, вена E). Делает «хорошо построенное рассуждение» структурно невозможным для самоссылочных конструкций. _(no-self-containment, russell, vein-E)_
- **`type1_blocks_reasoning`** - Нарушения типа-1 (недопустимая конституция: апелляция к силе, большая ложь) БЛОКИРУЮТ рассуждение на корню — не «слабый аргумент», а структурный отказ конституции. Привязывает именованные ошибки к ERR/уровневой структуре, а не к списку. _(type1, constitution, blocks)_

**Uniqueness - score 2 (methods).** Именованные ошибки привязаны к структуре конституции/уровней: тип-1 = недопустимая конституция (блокирует рассуждение), ERR без самосодержания, типы нарушений взаимоисключающи.
> _Caveat:_ Именованные ошибки и их типология известны; вклад — формальная привязка к ERR/уровневой структуре, не новая логика.

---

## #6 - `Architecture_of_Reasoning/ParadoxDissolution.v` - score 3 (new-framing)

**Paradox dissolution: 46 paradoxes, one mechanism (structural = self-referential level confusion)**

- **Topic.** A 46-paradox catalogue split into structural(13)/defective(25)/non-paradox(8); the proven counts; all 46 dissolvable; structural paradoxes proven self-referential (Liar malformed, Russell invalid, Carroll's tortoise demand illegitimate); the level-confusion diagnosis; ERR mapping; and LLM paradox patterns shown to be structural.
- **Role.** Vein-E flagship of the reasoning architecture: the unified paradox-dissolution engine. Self-contained.
- **Counts.** Qed 29 / Admitted 0 / axioms 0
- **Imports.** ToS_Arch: Architecture_of_Reasoning (local)
- **E/R/R.** _Elements:_ 46 парадоксов (структурные/дефектные/не-парадоксы); компоненты ERR. _Roles:_ парадокс = роль-самоссылочная путаница уровней; растворение как роль-ответ. _Rules:_ structural = self-referential; all_46_dissolvable; structural_implies_self_ref_46. _P4:_ конечный каталог 46 (Element); структурный парадокс = самоприменение уровня (запрещённый role-limit) → растворяется, не решается.
- **Classical counterpart.** Individual paradox resolutions (Tarski on the Liar, type theory on Russell, Carroll's regress) are known; NEW is the UNIFIED dissolution of 46 catalogued paradoxes via one mechanism — structural paradoxes are self-referential level confusions, all dissolvable; defective ones require rejection; non-paradoxes admit a solution.
- **Tags.** reasoning, paradox, dissolution, self-reference, level-confusion, vein-E, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `Dimension/ViolationType/HierarchicalLevel/level_lt/_le/valid_application/self_application_invalid/L2_applies_to_L1/L3_applies_to_L2` | Definition/Theorem | ★ самоприменение уровня недопустимо |
| `ParadoxCategory/StructuralSubtype/DefectiveSubtype/NonParadoxSubtype/category_diagnosis_domain/category_resolution/old_type_to_category` | Definition | категории парадоксов |
| `Paradox46/S1_Liar..S13_Cantor/D1_Sorites..D25_RossLittlewood/N1_MontyHall..N8_Raven/all_paradoxes_46/count_by_category/total_paradoxes_46/structural_count_13/defective_count_25/nonparadox_count_8/category_sum_correct` | Definition/Theorem | ★ каталог 46, счётчики 13/25/8 |
| `DissolutionStatus/dissolve_paradox_46/all_46_dissolvable/structural_46_dissolves/defective_46_requires_rejection/nonparadox_46_not_paradox` | Definition/Theorem | ★ все 46 растворимы по категории |
| `LiarStructure/liar_is_malformed/RussellStructure/russell_invalid/InferenceComponent/tortoise_demand/refuse_tortoise_demand/regress_stopped/paradox_is_level_confusion/is_self_referential/structural_implies_self_ref_46/all_structural_self_ref_46/S1_liar_self_ref/S10_russell_self_ref` | Theorem | ★ Лжец malformed, Рассел невалиден, регресс остановлен |
| `ERR_Component/err_to_level/err_level_confusion/carroll_is_err_confusion/Response/appropriate_response_46/paradoxes_require_dissolution/only_nonparadox_admits_solution/LLMParadoxPattern/llm_paradoxes_dissolvable/llm_self_ref_is_structural_46` | Definition/Theorem | ★ парадокс=путаница уровней ERR; LLM-паттерны структурны |

**Key lemmas (deep):**

- **`structural_implies_self_ref_46`** - Флагман вены E: ВСЕ структурные парадоксы (Лжец, Рассел, Греллинг, Карри, Берри, ...) доказуемо самоссылочны и суть путаница уровней (self_application_invalid). Один механизм растворяет 13 структурных парадоксов разом — та же диагональ/самоприменение, что блокирует russell_paradox в ядре ToS. Это объединяющее наблюдение, а не 13 отдельных решений. _(paradox-unification, self-reference, level-confusion, vein-E)_
- **`all_46_dissolvable`** - Все 46 каталогизированных парадоксов разрешаются по категории: структурные растворяются (level-confusion), дефектные требуют отклонения посылки, не-парадоксы допускают решение. paradoxes_require_dissolution vs only_nonparadox_admits_solution — содержательное различие «растворить» против «решить». LLM-паттерны парадоксов показаны структурными (применимость к AI). _(46-paradoxes, dissolution, categorized, llm)_

**Uniqueness - score 3 (new-framing).** Единое растворение 46 парадоксов одним механизмом: структурные = самоссылочная путаница уровней (доказано), дефектные = отклонение посылки, не-парадоксы = решаемы. Флагман вены E; тот же самоприменение-уровня, что блокирует Рассела в ядре ToS.
> _Caveat:_ Отдельные разрешения (Тарский/Лжец, типы/Рассел, Карролл) известны; вклад — их объединение в одну категоризированную ERR/уровневую диагностику для 46 парадоксов + перенос на LLM, не новое решение каждого.

