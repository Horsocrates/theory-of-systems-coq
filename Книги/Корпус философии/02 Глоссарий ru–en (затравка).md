# Глоссарий ru–en — затравка (2026-09-25)

Рабочая затравка двуязычного глоссария для перевода корпуса. Основа — девять английских
статей автора (PhilArchive), имена машинного слоя и значения со страниц сайта. Статус
«установлен автором» значит: термин уже стоит в английских текстах автора; «предложение» —
вариант переводчика; «требует решения автора» — выбор за автором. Термины, по которым
автор принял решение, переносятся в чистовой глоссарий (будет создан на этапе перевода).

## Срез G: терминология статей — затравка глоссария ru → en

### Сводка среза

- **Прочитано.** Все 9 статей целиком (≈76 тыс. слов, 12 877 строк). Машинный слой — только имена
  определений и теорем (`src/foundation`: Knowledge*, PerceptionTriad, BinarityVsTotality,
  TotalityNow, KnowledgeWillStatus, KnowledgeQuestionPath, ERRRepresentation, RoleLimit* и др.).
  Страницы сайта — для уточнения значений: Метафизика, Теория Систем, Логика (обзор, Порядок,
  Исключённое третье, Философия), Эпистемология (обзор, Правда и истина, Объективность,
  Интуиция), АР (обзор, Домены, индексы каталогов), Этика, Кодекс, Устав, Путь Мудрости,
  «Чего нет», Социальные Системы.
- **Состояние.** Примерно у 60% ядра терминов есть авторский английский (статьи, код, латиница
  в Томе «Математика»). Статьи — срез весны 2026 года, и канон с тех пор ушёл вперёд:
  Void → Источник; «это не дуализм» → дуализм начал; «L3 выведен» → L3 расщеплён; L5 → второй
  мета-закон; dissolution → «парадокс невозможен»; E/R/R → порядок Правила → Роли → Элементы;
  принцип домена 2 «Infinite Questions» → «Корня»; в каталоге ошибок было 150, теперь 158.
- **Где опоры нет.** Эпистемология правды и истины, этика, воля, ментал, эго, социальные
  системы, документы общины. Здесь глоссарий — это предложения.
- **Пять решений автора** (раздел 7): правда/истина · разум/ум/ментал · правота и правильность ·
  ярлык E/R/R · «растворение» парадоксов.
- Числа Qed в статьях (385, «390+», 7 767, 19 110, 19 660) — устаревшие снапшоты; в перевод они
  не идут (к тому же канон запрещает счётчики в прозе).

Статусы: **У** — установлен автором (статья, код или латиница Тома «Математика»);
**П** — предложение, конфликта нет; **Р** — требует решения автора.
ID статей: T18 = HORTLO-18 · T19 = HORTLO-19 · SD = HORTSD-4 · AO = HORTAO-17 · DV = HORDVA ·
PD = HORPDT · PM = HORPMC · TS = HORTOS · FD = HORFDT-5.

---

### 1. Таблица глоссария

#### A. Основание и метафизика

| ru | en у автора (ID + цитата) | варианты и конфликты | рекомендация | статус |
|---|---|---|---|---|
| Логика (система) | T19: “form = Logic (L1–L5, consciousness)”; код: `SLogic`, `logic_never_perceived` | строчная «logic» — дисциплина и структура | **Logic** — система (с прописной); logic — дисциплина | У |
| Источник | T19: “content = Void (fullness of potential, inexhaustible)”; FD: “a shared source in the Void”; код: `PosSource`, `source_inside_logic` | **конфликт:** Void (статьи, файлы VoidLogic*.v) против канона «полнота, а не пустота»; у Спенсер-Брауна void — пустота | **the Source**; Void — только в библиографических пометах | У (код) / конфликт |
| Свидетель | T19: “We formalize the observer as witness”; код: `Witness`, `only_witness_wills` | омоним: логический witness (экзистенциальный свидетель, `crit_level_witness`) на страницах «Формализация» и «Математика» | **witness**; см. §3 | У |
| самосвидетельствование | T19: “minimal self-referential determinacy self-witnessing” | — | **self-witnessing** | У |
| Свет | в статьях нет (только light cone); код: `PosLight`, `SLight`, `light_present` | комментарий к `SLight` в коде — «the first generated system», это снятая формула | **Light** | У (код) |
| проявленность как таковая · проявление · (не)проявленное | T19: “actualization is manifestation, not extraction”; код: `StManifest`, `StUnmanifest` | manifestness или manifestedness | Свет — **manifestness as such**; **manifestation**; **the manifest / the unmanifest** | У / П |
| Абсолют | нет ни в статьях, ни в коде | гегелевские коннотации | **the Absolute** + определение “one whole: Logic as rules, the Source as content” | П |
| мета-система | TS: “The meta-system already enforces this through the Laws of Logic” (в TS — иной смысл) | metasystem у Турчина (metasystem transition); на сайте то «мета-система», то «метасистема» | **meta-system** (через дефис, как у автора) | У (написание) |
| существование — статус | в статьях нет; T19 называет существование “the primary fact”; код: `status_as_system` (запись реестра) | — | **existence is a status, not a system** | П |
| первофакт · первопринцип · первоначало «А = существует» | T18: “The first principle proposed here is minimal: something exists.” | на сайте три имени одного | **first principle** (A = exists); «first fact» не вводить | У |
| различение · акт различения · первичное различение | T18: “its first necessary consequence: the act of distinction” | differentiation — синоним в статьях | **distinction · act of distinction · primary distinction** | У |
| различие | T18: “the difference itself is the sufficient reason” | — | **difference** (≠ distinction) | У |
| различённое · фон · граница | T18: “the differentiated (A)”, “the background (¬A)”, “the boundary of differentiation” | the distinguished / the differentiated | **the distinguished · the background · the boundary** | У |
| единица · отношение · структура (из различения) | T18: “Unit”, “Boundary”, “Relation”, “Structure” | — | **unit · relation · structure**; первоотношение — primordial relation | У |
| наполнение · содержание | T19: “form (Logic) applies to content (Void) at each step”; код: `Filling`, `SSource (* the filling inside the structure *)` | content (статьи) против filling (код) | см. §3: метафизика — **content**; заполнение ролей — **filling** | Р |
| полнота (потенциала) | T19: “ours is fullness (potential)” | plenitude сталкивается с «principle of plenitude» Лавджоя | **fullness of potential** | У |
| форма · структура | T18: “This form is the primordial structure.” | **двузначность в каноне:** в метафизике форма = Логика (структура), в ТС «форма — элемент в роли» (воплощение) | form · structure; для смысла ТС нужно решение (embodiment?) | Р |
| содержание-в-форме | T19: “A1 = content-in-form = determinate = new witness” | — | **content-in-form** | У |
| актуализация · потенциализация | T19: “Measurement actualizes the distinction”; код: `actualize` | — | **actualization · potentialization** | У / П |
| запись (встреч) | T19: “it is the record of their meetings”; код: `SelfRecord`, `record_is_subjective` | — | **record** | У |
| дуализм начал; «дуальна в основании, тринитарна в проявлении» | T19: “These are not two separate substances (dualism) but two aspects” | **конфликт:** статья отрицает дуализм, канон (МП-45) принял «дуализм начал» по имени | **dualism of principles (within one whole)**; “dual in its ground, triune in manifestation” | Р |
| реализм различений | T19: “what we call Distinction Realism” | — | **Distinction Realism** | У |
| энергии с уникальным различающим качеством | T19: “energies with unique distinguishing quality” | — | **energies with a unique distinguishing quality** | У |
| перспектива · локус | T19: “a locus at which the distinction registers” | — | **perspective · locus** | У |
| наблюдатель | T19: “The Observer as Witness” | — | **observer** | У |
| оператор | в статьях нет; код: `InsideOperator`, `OutsideOperator` | в Томе «Математика» сталкивается с operator (линейный оператор) | **operator** + пояснение при первом вхождении | У (код) |
| сознание | T19: “Consciousness is the term for that which witnesses.” | в триаде проявлений — potency (код PerceptionTriad) | **consciousness** | У |
| разум | в статьях нет; код PerceptionTriad: “act” | Reason / Intellect / Nous, см. §3 | **Intellect** (предложение) | Р |
| ум | — | wit / acumen / mind, см. §3 | **wit** — в тройке «рефлексия · ум · мудрость» | Р |
| мудрость | AO: “Tradition encodes accumulated wisdom” (бытовой смысл) | на сайте три формулы: «интеграция понятого» (Метафизика) · «целостность понятого» (Эпистемология, Философия) · «находить правду правильно» (Этика) | **wisdom**; формулу выровнять до перевода | П (+ вопрос) |
| ментал | в статьях нет; код PerceptionTriad: “medium” | the Mental / mind-stuff / mental medium, см. §3 | **the Mental** | Р |
| ментальное поле · объективное / субъективное поле | код: `KnowledgeMentalField`, `in_field`, `data_is_objective` | — | **mental field · objective / subjective field** | У (код) |
| мыслеформы | — | коннотация теософии (Besant & Leadbeater, “Thought-Forms”, 1901) | **thought-forms** + оговорка | П |
| воля · свобода воли · выбор направления / реакции | в статьях нет (free will — только в разборе Ньюкома); код: `will_never_zero`, `no_extinction` | — | **will · free will · choice of direction / choice of response** | П / У (код) |
| внимание | SD: “Noticing—the act of attention”; T19: “the maximum width of attention” | — | **attention** | У |
| эго · зона эго | код: `EgoZone`, `SelfRecord`, `ego_death` | — | **ego · ego zone** (“the zone of self-records”) | У (код) |
| разотождествление · овеществление · потенциализация зоны | код: `disidentification_keeps_zone`; DV: “Reification—treating abstractions as if they were concrete entities” | disidentification — термин Ассаджиоли, смысл близкий | **disidentification · reification · potentialization of the zone** | У |
| модальный квадрат: не может не быть · может быть — и есть · может быть, но нет · нет, и быть не может | код: `square_extremes`, `necessary_timeless`, `has_generating_step` | — | **modal square: cannot not be · can be — and is · can be, but is not · is not, and cannot be** | П |

#### B. Логика

| ru | en у автора (ID + цитата) | варианты и конфликты | рекомендация | статус |
|---|---|---|---|---|
| пять законов логики | T18: “identity, non-contradiction, excluded middle, sufficient reason, and order” | — | **the five laws of logic** | У |
| Тождество — устойчивость | T18: “The Law of Identity (L1): Stability” | канон запрещает на страницах индексы L1–L5 | **Identity (the Law of Identity) — stability** | У |
| Непротиворечие — исключительность | T18: “The Law of Non-Contradiction (L2): Exclusivity” | — | **Non-Contradiction — exclusivity** | У |
| Исключённое третье — тотальность; бинарность / тотальность | T18: “excluded middle (totality of the distinction)”; T19: “every act of distinction is binary”; код: `side_binarity`, `totality_is_about_now` | **конфликт:** в статьях L3 “derived” (TS, PM); канон — L3 расщеплён | **Excluded Middle**; **binarity** (теорема) / **totality** — “a counting regime about the now, not a thesis about the world” | У (термины) / П (формула) |
| Достаточное основание — самообоснованность | T18: “The Law of Sufficient Reason (L4): Self-Grounding” | T19 во введении: “the Principle of Sufficient Reason” | **the Law of Sufficient Reason — self-grounding**; аббревиатуры PSR не вводить | У |
| Порядок — упорядоченность | T18: “The Law of Order (L5): Ordering” | — | **Order (the Law of Order) — ordering** | У |
| мета-закон | T18: “one functions as a meta-law in which the rest are grounded” | **конфликт статуса L5:** в T18 L5 — “law of structure itself”; в T19 — “the meta-law”; на сайте L4 и L5 — оба мета-законы | **meta-law**; L5 — **the second meta-law** | У (+ конфликт) |
| Принцип Последовательности / Иерархии; горизонталь / вертикаль | T18: “Horizontal (Sequential)”, “Vertical (Hierarchical)” | в статьях — «dimensions», на сайте — «Принципы» | **Principle of Sequence / Principle of Hierarchy**; horizontal / vertical dimension | У / П |
| сохранение различений; прочтения A · B · C | T19: “Order is the law of preservation.” | — | **preservation**; readings: counting · content · structure | У |
| четыре принципа: Иерархия · Первичность критерия · Интенсиональное тождество · Конечная актуальность | T18: “Hierarchy (P1)”, “Criterion Precedence (P2)”, “Intensional Identity (P3)”, “Finite Actuality (P4)” | **конфликт:** в PM P1 = Wholeness, P2 = Complementarity, P3 = Hierarchy, P4 = Process | набор T18/TS: **Hierarchy · Criterion Precedence · Intensional Identity · Finite Actuality**; на страницах — без индексов | У (+ конфликт PM) |
| организованная множественность | T18: “the concept of system as organized multiplicity” | — | **organized multiplicity** | У |
| Логос | T19: “logic derives from logos—word, reason, structure, consciousness” | — | **Logos**, λόγος (logos) | У |
| критерий корректности | T19: “Well-Formedness Criterion: A construction is well-formed if and only if” | — | **well-formedness criterion** | У |
| смешение уровней | T19: “level-confusion” | — | **level confusion** | У |

#### C. Теория Систем

| ru | en у автора (ID + цитата) | варианты и конфликты | рекомендация | статус |
|---|---|---|---|---|
| Теория Систем | TS: “Theory of Systems: A First-Principles Foundation for Mathematics” | в статьях есть сокращение ToS | **Theory of Systems** | У |
| Правила · Роли · Элементы | T19: “We call this the E/R/R Framework: Elements, Roles, Rules.”; TS: “Rules determine Roles, Roles organize Elements.” | **конфликт:** ярлык E/R/R перечисляет в обратном порядке; Том «Математика» — “(Elements → Roles → Rules)”; Этика, шаг 4 — «Роли (как) · Правила (почему)», тогда как ТС: Правила — как, Роли — зачем | **Rules · Roles · Elements** (Rules — how, Roles — why, Elements — what); ярлык E/R/R — только в «Формализации» | Р |
| роль · правило · элемент | T19: “Roles are the why of the system” | — | **role · rule · element**; Element с прописной — в Томе «Математика» | У |
| статус | TS: “A Status is a state assigned by Rules to elements occupying roles” | — | **status** | У |
| позиция | T19: “as the definition of positional status” | в Уставе три рода мест: роль / функция / позиция | **position** | У |
| конституция системы | TS: “Constitution (Rules): A predicate C specifying the system's governing principles”; код: `Constitution` | в статье конституция = правила; в каноне — правила + необходимые роли | **constitution** (с новым определением) | У |
| необходимая (критичная) · разрешённая (дополнительная) роль | код: `RNecessary / RPermitted / RForbidden` | — | **necessary · permitted role** | У (код) |
| порождающий порядок (Цель → Правила → Роли → Элементы); порождающий шаг | в статьях нет; код: `has_generating_step` | generative order — термин Бома (1987) | **generating order** (Purpose → Rules → Roles → Elements); **generating step** | Р |
| теорема представления (система = основание ⊕ структура ⊕ уровень) | в статьях нет; код: `err_representation`, `triple_not_complete` | — | **representation theorem** (system = ground ⊕ structure ⊕ level) | У (код) |
| цель · задача системы · эффективность | — | goal / purpose; efficiency / effectiveness | цель — **purpose**; задача — **task**; эффективность — **effectiveness** («мера результата», а не экономия) | П |
| уровень · ярус · вложенность | T19: “E/R/R and Levels of Nesting” | — | **level · tier · nesting** | У |
| мягкая / жёсткая система | — | сталкивается с soft/hard systems (Checkland, SSM) | см. §2 | Р |
| открытая / закрытая система | — | сталкивается с open/closed system (Берталанфи, термодинамика) | см. §2 | Р |
| связь (правило взаимодействия) | FD: “the connection i between the two sides of a distinction” (в FD — математический смысл) | bond / link / coupling | **connection** | П |
| эмерджентность | AO: “It is an emergent property—a pattern that arises”; код: `emergent`, `emergence_measure` | — | **emergence** | У |
| роль-предел | в статьях нет; Том «Математика»: “role-limit” (около 100 раз); код: `RoleLimit`, `role_limit` | limit role / limiting role, см. §3 | **role-limit** | У (код, Том) |
| процесс | T18: “infinity is a quality of processes (unboundedness)” | — | **process** | У |
| конечная актуальность | T18: “Finite Actuality (P4): Any system is finite at any moment” | — | **Finite Actuality** | У |
| потенциальная / актуальная бесконечность | TS: “Actual Infinity (rejected)” / “Potential Infinity (embraced)” | на сайте ещё «процессная бесконечность» | **potential / actual infinity**; process infinity | У |
| финитизация · граница финитизации | в статьях нет; код: `FinitizationBoundary`, `computation_is_finitization_boundary`; HIGHLIGHTS: “Finitization boundary = constructivity boundary” | ≠ finitism (Гильберт) | **finitization · finitization boundary** | У (код) |
| резолюция порядком (назначение статуса Порядком) | TS: “L5-Resolution: Determinism from Order”; T19: “L5 Status Assignment Principle” | индекс L5 на страницах запрещён | **resolution by Order**; status assignment by Order | У / П |
| срез · состояние · шаг · ход | код: `deep_beyond_slice`, `current_not_in_slice` | snapshot / cross-section | **slice (projection) · state · step · move** | П |
| аттрактор · зонная статистика · системы-записи | — | — | **attractor · zone statistics · record-systems** | П |
| границы систем проводит оператор; системы пересекаются элементами | — | — | “system boundaries are drawn by the operator”; “systems intersect in elements” | П |

#### D. Эпистемология

| ru | en у автора (ID + цитата) | варианты и конфликты | рекомендация | статус |
|---|---|---|---|---|
| правда | AO: “a single criterion: orientation toward truth” | в статьях одно truth покрывает и правду, и истину | **truth**, см. §3 | Р |
| истина | SD: “Truth is not content-matching but structural alignment.” | — | **exact truth** (предложение), см. §3 | Р |
| честность | SD: “Honesty of Inference. Four requirements” | — | **honesty** | У |
| установка · настройка | AO: “orientation toward truth”; код: `Tuning`, `Intent: ToTruth / ToOther` | attitude / stance / set (у Узнадзе установка = set) | установка — **orientation**; настройка — **attunement** (в коде tuning) | П |
| правота | — | rightness / being right / correctness, см. §3 | **being right** | Р |
| ложь | AO: “Big Lie Technique”; код: `is_lie`, `lie_by_intent` | falsehood двусмысленно (и утверждение, и свойство) | **lie** (статус акта), lying | У |
| не-правда | код: `UntruthPath`, `CsUntrue` | untruth в словарях — ещё и эвфемизм «лжи», а канон разводит не-правду и ложь | **non-truth** (или untruth — по коду) | Р |
| честная ошибка | код: `is_honest_error` | — | **honest error** | У (код) |
| искажение · замещение | код: `distortion_needs_knowledge`, `substitution_always_available` | в DV Object Deformation / Object Substitution — другой смысл | **distortion · substitution** | У (код) |
| истинно / ложно (статусы содержания) | код: `CsTrue`, `honest_iff_status_matches` | — | **true / false** | У |
| объективность · субъективность; занятая позиция | SD: “The Principle of Objectivity. Focus on truth excludes focus on confirmation.” | — | **objectivity · subjectivity**; an occupied position | У / П |
| интуиция | AO: “Genuine intuition arises from extended practice in domains with clear feedback.” | — | **intuition** | У |
| усмотрение · дискурсия | SD: “intuitive insight”; код: `KnowledgeInsight`, `usmotrenie_*` (транслит!) | intellection / eidetic seeing; discursion / discursus | **insight · discursive thought** | У / П |
| знание | SD: “knowledge is not a state but an achievement” | — | **knowledge** | У |
| данные · считывание · информация · запись | SD: “data become information by being noticed”; T19: “record” | — | **data · reading · information · record** | У |
| качества · характеристики | SD: “Qualities: categories by which things differ” | — | **qualities · characteristics** | У |
| понимание | SD: “Understanding of what was recognized” | — | **understanding** | У |
| мнение → знание-что → понимание | — | doxa → orthē doxa → epistēmē | **opinion → knowledge-that → understanding** | П |
| знание-о · знание-как · присутствие · передача · дистиллят | код: `knowledge_that_is_distilled`, `presence_is_root` | **конфликт:** в коде знание-о названо “that”, на сайте “знание-что” — отдельная ступень; у Джеймса — knowledge-about, у Райла — knowing how | **knowledge-about · knowledge-how · presence · transmission · distillate** | Р |
| поле · срез · зазор; порог · канал · глубина | код: `in_field`, `no_gap_no_pull`, `has_channel`, `subject_needs_threshold` | — | **field · slice · gap; threshold · channel · depth** | У (код) |
| познаваемость | код: `c_knowable` | — | **knowability** | П |
| встреча · контекст · путь · закрытие | — | — | **encounter · context · path · closure** | П |
| суть · проявление | код: `essence_always_manifest`, `manifestation_varies_identity_stands` | — | **essence · manifestation** | У (код) |

#### E. Архитектура Рассуждения

| ru | en у автора (ID + цитата) | варианты и конфликты | рекомендация | статус |
|---|---|---|---|---|
| Архитектура Рассуждения | T18: “Article 1 in the series ‘Architecture of Reasoning’” | DOCX-книга называется «Архитектура Размышления» | **Architecture of Reasoning** | У |
| домен рассуждения | SD: “A domain is a logical territory” | stage и step автор сам отверг | **domain of reasoning** | У |
| шесть доменов | SD: “Recognition, Clarification, Framework Selection, Comparison, Inference, and Reflection” | «Выбор рамки» дословно — choice of frame | **Recognition · Clarification · Framework Selection · Comparison · Inference · Reflection** | У |
| направляющие принципы: Присутствия · Корня · Объективности · Рационализма · Ограничения | SD: “Presence, Infinite Questions, Objectivity, Presence (in new application), Rationalism, Limitation” | **конфликт:** Д2 — на сайте «Корня», в статье Infinite Questions; Д4 — на сайте «узловой» (три принципа), в статье Presence | **Principle of Presence · of the Root · of Objectivity · of Rationalism · of Limitation** | Р (Д2, Д4) |
| аспекты реальности: данность · определённость · многоаспектность · связность · необходимость · неисчерпаемость | SD: “givenness … determinateness … multi-aspectuality … connectedness … necessity … inexhaustibility” | — | как у автора | У |
| возвраты: корректирующий · углубляющий · расширяющий | SD: “Corrective return”, “Deepening return”, “Expanding return” | — | как у автора | У |
| ошибка рассуждения · заблуждение · софизм | AO: “a fallacy is a violation of the architecture of reasoning” | на сайте заблуждение — ненамеренное, софизм — намеренное | **fallacy** (родовое) · fallacy / error (ненамеренное) · **sophism** | У / П |
| Тип 1: нарушения условий; 1.A ошибки постановки вопроса; 1.B подмены рассуждения (манипуляции) | AO: “Type 1: Violation of Conditions”; “Defective Questions”; “Manipulations” | **конфликт:** коды сайта 1.A/1.B (1.B.1–15) не совпадают с кодами статьи 1.1/1.2 (1.2.1–10); ошибок 38 против 36 | **Violations of Conditions · Errors of Question-Setting (Defective Questions) · Substitutes for Reasoning (Manipulations)** | У / Р (сверка каталога) |
| Тип 2: нарушения доменов | DV: “Type 2: Domain Violations” | коды подтипов расходятся (на сайте 2.3.5, 2.4.5) | **Domain Violations** | У |
| Тип 3: нарушения последовательности | AO: “Type 3: Violation of Sequence” | на сайте 3.2 «Обратное движение», 3.3 «Инверсия бремени»; в статье 3.1–3.3 | **Violations of Sequence** | У |
| Тип 4: синдромы (когнитивного диссонанса · системного искажения) | AO: “Cognitive Dissonance Syndromes”, “Systemic Distortion Syndromes” | на сайте 4.1.2 «Стабильный диссонанс» и 4.1.3 — в статье их нет | **Syndromes** | У |
| Тип 5: контекстно-зависимые методы (интуитивное · традиционное · косвенное познание) | AO: “Type 5: Context-Dependent Methods”; “Intuitive Cognition” | — | как у автора | У |
| парадокс структурный · дефектный · не-парадокс | PD: “structural paradoxes”, “defective paradoxes”, “non-paradoxes” | — | как у автора | У |
| растворение (парадокса) | PD: “They require dissolution—identification of where the formulation goes wrong” | **конфликт:** правило канона 4 («растворяет» — дефект), но обзоры АР и «Каталога парадоксов» пишут «растворяются, а не решаются» | см. §2 | Р |
| вопрос (указывающий акт): полярный · восполняющий · выборный | SD: “directed thinking that moves from question to justified answer” | — | **question** (a pointing act): polar · completing · choice question | П |

#### F. Этика и социальное

| ru | en у автора (ID + цитата) | варианты и конфликты | рекомендация | статус |
|---|---|---|---|---|
| правильно / неправильно; правильность; «правильное = логика = порядок» | — | right / wrong или correct / incorrect, см. §3 | **right / wrong; rightness**; “the right = logic = order” | Р |
| добро / зло | — | — | **good / evil** | П |
| благо / вред | — | the good / weal | **benefit / harm** (the good не брать: сталкивается с добром) | П |
| намерение · умысел | — | — | **intention · intent** | П |
| эгоизм (установка на запись) | — | selfishness (бытовое) | **egoism** — “an orientation toward the self-record” | П |
| должное · долг | — | — | **the ought · duty** | П |
| совесть («со-знание») | — | со-весть ↔ con-scientia | **conscience** | П |
| добродетель · порок · склад | — | character / hexis | **virtue · vice · disposition** | П |
| акрасия | — | — | **akrasia** | П |
| истинный порядок · согласование вверх | — | — | **true order · upward concordance** | П |
| возмещение · наказание | — | compensation | **restitution · punishment** | П |
| справедливость | — | righteousness (религиозное) | **justice** | П |
| Гильдия Философов | — | **конфликт на сайте:** в «Социальных системах» — «Философская Гильдия» | **Guild of Philosophers** | П (+ сверка) |
| управление-«садовник» | — | ср. McChrystal, “Leading like a gardener” | **gardener governance** — “a gardener, not an allocator” | П |
| тяга · впору · порог · пул | — | — | **pull · fit · threshold · pool** | П |
| слушатель · последователь · философ | — | — | **listener · follower · philosopher** | П |

#### G. Имена сайта и документов

| ru | en у автора | варианты и конфликты | рекомендация | статус |
|---|---|---|---|---|
| Путь Мудрости | — | Way of Wisdom (религиозно-даосский оттенок) | **The Path of Wisdom** | П |
| «Вера в Мудрость» (община) | — | Faith / Fidelity / Trust in Wisdom | **Faith in Wisdom** + глосса «вера = верность основанию» | Р |
| Библиотека | — | — | **Library** | П |
| Направления | — | Directions (калька) / Fields | **Branches** | П |
| «Чего нет, и быть не может» | код: `registry`, `all_registry_illegal` | Registry of the Impossible | **What Is Not, and Cannot Be** | П |
| Устав | — | Statute / Rule (монашеский «устав») | **Charter** | П |
| Этический Кодекс | — | Ethical Code | **Code of Ethics** | П |
| Клятва Маат | — | Ma'at | **Oath of Maat** | П |
| «Истина (Правда) превыше всего» | — | на сайте две версии девиза | **Truth above all** — одна для обеих | П |
| Формализация | TS: “Formal Verification”; formalization (58 раз) | — | **Formalization** | У |
| имя автора | Horsocrates — T18, T19 (подпись), PD, PM, TS, FD; Horsokrates — SD, AO, DV и сноски T19 | сайт, код и PhilArchive: Horsocrates | **Horsocrates** | У |

---

### 2. Термины без устоявшегося английского: варианты и доводы

1. **Источник.** (a) *the Source* — плюсы: так в коде (`PosSource`, `source_inside_logic`), прямое
   значение, никакой пустоты в слове. Минус: бытовое слово, нужна прописная. (b) *the Void* — плюс:
   так в T19 и FD. Минусы: прямо противоречит канону «полнота, а не пустота»; совпадает с void
   Спенсер-Брауна, с которым сама T19 спорит. (c) *the Plenum* — плюс: «полнота». Минус: оттенок
   схоластики и физики. → **(a).**
2. **Свет и проявленность.** *Light* (свет ишрака у Сухраварди; код). Для «проявленности»:
   *manifestness* — так в английских переводах Хайдеггера передают Offenbarkeit — против громоздкого
   *manifestedness* или описательного *self-disclosure*. → **Light — manifestness as such.**
3. **Дуализм начал.** (a) *dualism of principles* — канон принял «дуализм» по имени; минус: слово
   principle занято (P1–P4, first principle). (b) *duality of the ground* — «основание» = ground,
   звучит мягче «dualism». (c) *dualism of archai* — ἀρχαί есть на странице; минус: учёно. →
   заголовок “Two Principles: the Duality of the Ground”, в тексте “a dualism of principles within
   one whole”.
4. **Порождающий порядок.** (a) *generating order* — созвучно коду `has_generating_step`.
   (b) *generative order* — естественнее, но это термин Бома (Bohm & Peat, 1987). (c) *order of
   construction* — страница сама говорит «порядок построения», но «порождение» теряется. → **(a).**
5. **Мягкая / жёсткая система.** (a) *soft / hard system* — коротко, по имени страницы; минус:
   англоязычный читатель услышит методологию SSM Чекленда. (b) *fallible / infallible system* —
   ровно критерий «возможен ли неправильный выбор»; минус: звучит оценочно. (c) *open-choice /
   fixed-outcome system*. → **(a) + определение при первом вхождении и сноска о Чекленде.**
6. **Открытая / закрытая система** (подбор ведёт воля / закон). (a) *open / closed* — минус:
   Берталанфи и термодинамика. (b) *will-steered / law-steered* — ровно критерий. (c) *manual /
   automatic* — сама страница так поясняет в кавычках; минус: разговорно. → (b) и «open/closed» в
   скобках; **Р**.
7. **Связь (правило взаимодействия).** *connection* (нейтрально; в FD есть в матсмысле), *bond*
   (химический оттенок), *link* (слабо). → **connection**.
8. **Установка / настройка.** *orientation* (у автора: AO, «orientation toward truth») против
   *attitude* и *set* (у Узнадзе установка = set); *attunement* против *tuning* (так в коде). →
   **orientation; attunement**.
9. **Усмотрение / дискурсия.** *insight* (файл KnowledgeInsight) против *intellection* и *eidetic
   seeing*; *discursive thought* против редкого *discursion*. → **insight · discursive thought**.
10. **Знание-о / знание-что / знание-как.** *knowledge-about* (у Джеймса) · *knowledge-that* (у
    Райла) · *knowledge-how*. В коде знание-о названо “that” — это конфликт. → оставить три
    английских имени и переименовать в коде при случае; **Р**.
11. **Не-правда.** *non-truth* (калька с дефисом, как «не-правда»; однозначно) против *untruth* (так
    в коде, но в словарях это и эвфемизм «лжи» — ровно то смешение, которое канон запрещает)
    против *falsity* (годится для «ложно», но теряет связь с «правдой»). → **non-truth**; **Р**.
12. **Растворение парадокса.** (a) *dissolution* — так в PD, и это стандарт аналитической традиции;
    минус: канон считает «растворяет» дефектом. (b) *the paradox does not form / is ill-formed* —
    так в каноне («в реальности парадоксов нет»; в ТС: «не формируется»). (c) *diagnosis of the
    construction error*. → в новой прозе (b) и (c), «dissolution» — только в ссылке на PD; **Р**.
13. **Направления.** *Branches* — сама страница ТС строит метафору корень — ствол — ветви, а
    «branches of philosophy» — идиома; против *Fields* и кальки *Directions*. → **Branches**.
14. **Устав.** *Charter* (учредительный документ общины; не путается с constitution ТС, хотя Устав
    определён как «записанная конституция») против *Statute* (юридично) и *Rule* (монашеский
    оттенок). → **Charter**.
15. **«Вера в Мудрость».** *Faith in Wisdom* (естественно, но религиозно) · *Fidelity to Wisdom*
    (ровно по определению «верность основанию», но тяжеловесно) · *Trust in Wisdom*. → **Р**.
16. **Принцип Корня (домен 2).** *Principle of the Root* · *Principle of Grounding* · прежнее
    *Principle of Infinite Questions* (SD). → **Р** (сайт и статья расходятся).
17. **Мета-система.** *meta-system* (через дефис, как в TS) против *metasystem* (у Турчина это иной
    смысл). → **meta-system**.
18. **Ярлык E/R/R.** (a) Сохранить “E/R/R Framework” как имя собственное — это бренд статей и имён
    файлов кода. (b) В прозе писать “the Rules–Roles–Elements triad”, а E/R/R оставить
    «Формализации». (c) Переименовать ярлык в R/R/E. → **(b)**; **Р**.
19. **Мыслеформы.** *thought-forms* — точная калька, но с теософским следом; альтернатива
    *thought-shapes* неидиоматична. → thought-forms + оговорка.

---

### 3. «Непереводимые пары»

#### 3.1 Правда / истина
Канон: правда — как есть (онтологична, ничья, «стоит сама»); истина — объективная правда, как
**именно** есть; различие в точности, а не в объёме. Страница «Правда и истина» сама пишет, что
английский обходится одним truth (← др.-англ. trēowþ «верность», корень true, trust). В статьях
одно truth покрывает обе стороны: “orientation toward truth” (AO) — это правда;
“Truth is not content-matching but structural alignment” (SD) — это истина.

| стратегия | плюсы | минусы |
|---|---|---|
| **truth / exact truth** (калька определения) | Формула переводится один к одному: “Truth is how it is; exact truth is how exactly it is.” Различие по точности встроено в имя; честность = “orientation toward truth” | Истина получает составное имя; неловко звучат «знать — держать истину» и «истина — это логика»; прилагательное true общее для обеих |
| **truth / verity** | Два однословных термина | Verity архаично и торжественно, читается как «высшая истина», то есть различие по объёму — против канона. Латинская линия veritas на самой странице отнесена к «верности» |
| **pravda / istina** (транслит + глосса) | Сохраняет русскую традицию (Михайловский: правда-истина и правда-справедливость; Флоренский; «Жить не по лжи»), помечает уникальность пары | «Pravda» у англоязычного читателя — газета; тяжело в сплошном тексте; у Михайловского пара значит другое, и чужой смысл придёт вместе с транслитом |
| **truth / objective truth** (по букве определения) | Авторская формула «истина — объективная правда» | Подсказывает, что правда «субъективна», а канон это отрицает (правда ничья) |
| **truth / Truth** (прописная) | Коротко | Прописная сигналит объём и ценность — против канона |

**Рекомендация:** truth / exact truth — там, где различие — тема страницы («Правда и истина»,
«Объективность», «Эпистемология», «Метафизика»); при первом вхождении глосса “truth (Russ. pravda:
how it is) · exact truth (Russ. istina: how exactly it is)”. Где русский текст употребляет
«истину» без противопоставления (девизы, «держать истину»), ставить truth; девиз — “Truth above
all”. Попутно: в Уставе строка «Истина — объективная правда: то, как есть» определяет истину
формулой правды; до перевода её стоит выправить. **Р.**

#### 3.2 Честность / правота
- **Честность → honesty.** Установлено автором: SD “Honesty of Inference”, AO “orientation toward
  truth”. Этимологии совпадают: честь ← *čьstь «чтить» и honesty ← лат. honestas ← honos «честь».
  Определение канона: “an orientation of consciousness toward truth; binary; it excludes lying and
  only lying”.
- **Правота.** Канон: правота = правда, «прав тот, кто видит и говорит, как есть». Англ. *right* ←
  др.-англ. riht «прямой» ← и.-е. *h₃reǵ- «выпрямлять»; из того же корня *rule* (regula) и
  *correct* (corrigere). Значит, в английском воспроизводится гнездо правило — правый — правильный —
  правота (rule — right — correct — rightness); выпадает только правда (truth). Стратегии:
  (a) *being right* — естественно в эпистемическом смысле, и слово «rightness» остаётся для этики;
  (b) *rightness* — однословно, но в английской этике rightness — это правильность поступка, и
  выйдет столкновение с «правильно/неправильно»; (c) *correctness* — годится для «правильного
  ответа», но теряет связь с правдой; (d) *rectitude* — моральный оттенок, мимо. →
  **(a) being right**; «правильно / неправильно» — **right / wrong** (английская пара «the right vs
  the good» точно ложится на авторское «правильное первично; благо — плод правого»); в технических
  контекстах допустимо correct. **Р.**

#### 3.3 Свидетель
- Русское: свидетель ← съвѣдѣтель (съ- «с, вместе» + вѣдѣти «знать»), со-ведающий. Английское:
  witness ← др.-англ. witnes «знание, разумение; свидетельство» ← witan «знать». Оба слова
  восходят к и.-е. *weid- «видеть → знать»: в славянской и германской ветвях победило «знать»
  (вѣдѣти, witan), в латыни — «видеть» (videre). Поэтому тезис страницы «слово указывает не на
  зрение, а на знание» переходит в английский без потерь, а корень ещё и показывает, что знать —
  значит «увидеть».
- Приставки «со-» у witness нет, но она есть у лат. con-scire: consciousness и conscience
  соответствуют «со-знанию» и «со-вести». На сайте «совесть — со-знание» уже есть, так что гнездо
  переводится целиком: witness · consciousness · conscience.
- Бонус: из того же *weid- wit и wise / wisdom. В английском witness — wit — wisdom — одна семья;
  это держит сайтовую линию свидетель → знание → мудрость.
- Контраст: санскр. sākṣin (sa + akṣa, «с глазами»), встречающийся на странице «Метафизика»,
  указывает именно на зрение; это стоит пояснить в примечании.
- Стратегии: (a) **witness** (авторское) + этимологическое примечание; (b) калька *co-knower* —
  сохраняет «со-», но это неологизм без опоры; (c) транслит — не нужен. → **(a).** Риск: логический
  witness (экзистенциальный свидетель в коде и на странице «Формализация») — там снабдить пометой.

#### 3.4 Разум / ум / мудрость
Канон: Разум — действующая способность свидетеля, «то, что воспринимает данные и понимает
воспринятое»; в триаде — акт (Сознание — потенция, Ментал — среда). Ум — «навык владения
разумом». Мудрость — «интеграция» или «целостность понятого»; в Этике — «находить правду
правильно».

| термин | вариант | плюсы | минусы |
|---|---|---|---|
| Разум | **Intellect** | Лат. intellectus = «схватывание, понимание» — страница сама так противопоставляет intellectus и ratio; попадает в «то, чем понимают»; не сталкивается с reasoning и sufficient reason | Звучит «кабинетно»; теряется родство разум — разуметь |
| | Reason | Словарный эквивалент; Vernunft = разум = reason в обеих традициях перевода Канта | Сталкивается с Sufficient Reason и reasoning (всё направление АР); в английском reason — дискурсивный вывод, а канонический Разум ещё и воспринимает |
| | Nous (транслит) | Страница выводит ум из νοῦς / νοέω «замечать» — смысл точный | Эзотерично; у неоплатоников Nous — ипостась, а не способность свидетеля |
| Ум | **wit** | Старый смысл «умственная способность, сметка»; однокоренное с witness и wisdom; тройка «reflection · wit · wisdom» звучит естественно | Современное wit — «остроумие» |
| | acumen | «Навык, острота» | Латинизм с деловым оттенком |
| | mind | Привычно | Слишком широко; сталкивается с Разумом и Менталом |
| Мудрость | **wisdom** | Прямой эквивалент (sophia) | — (выровнять русское определение: «интеграция» или «целостность»; в англ. — integration / wholeness; integrity не брать, в английском это и «честность») |

→ **Intellect · wit · wisdom**; при первом вхождении глосса “Intellect (Russ. razum; cf. Gk. nous,
Lat. intellectus)”. **Р.**

#### 3.5 Ментал
Неологизм: среда восприятия, содержимое — мыслеформы, в работе — ментальное поле.
(a) **the Mental** — субстантивированное прилагательное; параллель к «the Mental» у Шри Ауробиндо
и «mental plane» у теософов; плюс: прозрачно и держит однословный ритм триады «Consciousness ·
Intellect · the Mental»; минус: эзотерический след. (b) *mind-stuff* — так Вивекананда переводил
читту (среду, где возникают вритти), а автор сам опирается на Йога-сутры (нирбиджа-самадхи);
плюс: точная традиционная параллель; минус: звучит неформально. (c) *mental medium* — описательно
и ясно, но это не имя. → **(a)**; ментальное поле — mental field (так в коде). **Р.**

#### 3.6 Наполнение
Русское гнездо: наполнение — полнота — полный («Источник — наполнение», «Источник — полнота
потенциала»); в ТС роли заполняются элементами. (a) *content* — пара content/form из T19,
стандарт философии; минус: теряется корень «полн-», двусмысленность content/contents.
(b) *filling* — так в коде (`Filling`; комментарий «the filling inside the structure»); плюс:
fill — full — fullness держат корень; минус: бытовое звучание. (c) *plenum / plenitude* — плюс:
«полнота»; минус: схоластика и «principle of plenitude» Лавджоя. → **content** — в метафизической
паре «content within structure / form»; **filling** — для ролей, заполняемых элементами (ТС,
тождество); **fullness** — для полноты. Отдельный вопрос автору: в ТС «форма — элемент в роли», а
в метафизике форма — это Логика; в английском (form = Aristotelian form) это столкновение станет
видно сразу. **Р.**

#### 3.7 Роль-предел
Канон: роль, которую не занимает никакой элемент ни на каком шаге; приближение без прибытия.
(a) **role-limit** — так в Томе «Математика» (около 100 раз) и в коде (`RoleLimit`, `role_limit`);
дефисный аппозитив, как philosopher-king. Минус: по английскому правилу вершина сложения —
последнее слово, и читатель может понять «предел роли». (b) *limit role* — идиоматично (вершина
role), но расходится с кодом и Томом. (c) *unoccupiable role / asymptotic role* — самоочевидно,
но теряет «предел» (limit), то есть связь с математикой и границей финитизации, а unoccupiable —
ещё и отрицательное имя, что против правила позитивной онтологии. → **(a) role-limit** с глоссой
при первом вхождении: “a role that no element occupies at any step — approach without arrival”;
пара — **Element / role-limit**. **У.**

---

### 4. Профиль английского стиля автора

- **Регистр.** Академическая аналитическая философия: авторское we/our/us (≈1,5–7 на 1000 слов; меньше всего в DV), «this paper
  argues / we show». Каркас статьи: Abstract → Keywords → Introduction (Context and Motivation ·
  Central Thesis · Scope · Paper Structure) → разделы → Objections and Replies → Conclusion →
  References; внизу — «Article N in the series “Architecture of Reasoning”». Сноски с полными
  ссылками. Разделы честного объёма: “Scope of Verification”, “three levels of rigor”, “We
  distinguish what is established from what is conjectured”.
- **Фраза.** В среднем ≈15–25 слов (оценка по пунктуации; таблицы и код искажают счёт). Короткие
  афористичные замыкания: “To be is to be something…”, “We lose pathologies, not mathematics.”,
  “What remains is clarity.” Длинные тире без пробелов — очень часто (≈6–20 на 1000 слов там, где
  извлечение из PDF их сохранило: T18, SD, AO, DV, FD), для
  определений через приложение: “differentiation—distinguishing A from not-A”. Оксфордская
  запятая; фигурные кавычки “…”; курсив для ключевого слова.
- **Законы.** Шаблон: “The Law of X (Ln): Property” → Formulation → Derivation from Distinction →
  Structural Property → Contraposition; дальше заметки (Note on Dialetheism, Note on
  Intuitionism); формулы A = A, ¬(A ∧ ¬A), A ∨ ¬A; сводная таблица Law · Name · Structural
  Property · Status. Индексы L1–L5 и P1–P4 стоят везде; канон 6 требует в переводе заменить их
  именами.
- **E/R/R.** “E/R/R Framework (Elements/Roles/Rules)”; вопросы what · why · how ↔ L1 · L4 · L5;
  схема “Rules —determine→ Roles —distinguish→ Elements”; в TS формальное определение идёт “in
  order of precedence”: Constitution (Rules), Relations (Roles), Domain (Elements). Порядок
  предшествования у автора уже R → R → E; обратный только ярлык.
- **Шаблоны разборов.** В каталогах: Definition / Mechanism / Example / Diagnostic question /
  Response / Other fallacies in this subtype. В парадоксах: Domain 1 … 6 → First signal → Key
  insight → Diagnosis → Dissolution → Lesson. Спор: Objection / Reply. Сквозной ход — элентический
  («to argue against the Law of Order is to instantiate it»).
- **Устойчивые обороты.** determinate existence, primary distinction, act of distinction, structural
  property, self-grounding, rather than (2–14 на статью), not merely, in the same respect, as such,
  Consider…, Therefore…, Crucially… Контраст «X is not A but B» — 0,6–3,4 на 1000 слов; всех
  отрицательных форм (is/are/does not) — 4,5–8,2 на 1000 слов, больше всего в T18, T19, SD
  (7,3–8,2). **Эту привычку не переносить в перевод:**
  правило 1 (позитивная онтология) действует и для английского.
- **Греческое и прочее.** Греческие философские слова — только латиницей, без греческого шрифта и
  без макронов (logos, aporia, elenctic); санскрит без диакритики (atman, maya, sunyata, samadhi);
  зато в SD индийские и арабские имена с макронами (Dignāga, al-Fārābī, Ibn Sīnā). Латинские
  вкрапления: ad hoc, qua, façon de parler, ex nihilo, onus probandi, a priori, reductio. Для
  перевода — стандарт сайта: «ἀλήθεια (alētheia)», греческий шрифт + транслитерация с макронами.
- **Орфография — американская, последовательно:** -ize/-ization (organized ×36, formalization
  ×58), color, behavior, center, favor, judgment, defense, toward, artifact, skeptic, traveled,
  modeled. Единственное исключение — catalogued (×3, AO) и cataloguing (×1, SD) рядом с catalog
  (×18). → в переводе американская, «cataloged».
- **Прописные.** Law of Order, Theory of Systems, Logic и Void как системы, E/R/R Framework, имена
  доменов (Recognition…) и принципов (Principle of Presence).

---

### 5. Карта опоры: страница ↔ статья ↔ разделы

| страница сайта | статья-опора | разделы статьи | годится ли как английская основа |
|---|---|---|---|
| Логика (обзор) | T18 (на странице объявлена «Опорой») | §§1–7, прил. A (P1–P4 и их доказательства) | **Да:** «Основание», «Акт различения», «Законы», «Единство законов», «От законов к принципам» почти один к одному. Исторический вход (Гераклит — Хайдеггер) — без опоры |
| Тождество · Непротиворечие · Исключённое третье · Достаточное основание | T18 §4.1–4.4 (+ Note on Dialetheism, Note on Intuitionism); T19 §8 | формулировки, выводы, контрапозиция | **Частично:** история и возражения (Брауэр — Гильберт, трилемма) — из русского тома АР |
| Порядок | T19 (объявлена «Опорой») | §2 история; §3–4 два измерения; §4.3 назначение статусов; §6 самообоснование; §7 онтологический статус; §10–11 сохранение и физика | **Да, почти целиком** |
| Метафизика | T19 §12 (два аспекта первопринципа, наблюдатель как свидетель, время из наблюдения, неуничтожимость, Distinction Realism, Спенсер-Браун); FD §3.3 и §8 | — | **Частично и с поправками канона:** Void → Source; «not dualism» → дуализм начал; Света, Абсолюта, Разума, Ментала, воли, эго в статьях нет |
| Теория Систем | TS ч. I §2.1–2.4, ч. IV §5.1; T19 §4.2–4.3; PM §1.2 | триада, иерархия, P1–P4, роль и статус, корректность, сравнение с ZFC | **Частично:** нет порождающего порядка, теоремы представления, мягкой/жёсткой системы, взаимодействия, динамики, эмерджентности, роли-предела |
| Формализация | TS ч. II; PM; FD §10; T19 §13 | архитектура Coq, аксиомы | Структура — да; **все числа устарели** |
| Математика (обзор, Том) | PM; TS §3.2, §5.1–5.2; T18 §6.3 | P4, RealProcess, IVT/EVT/BW/HB, «What we lose» | Частично (главы I–IV) |
| Архитектура Рассуждения (обзор) | SD §1–2, §4, §6–7; AO §1–2; PD §1–2 | тезис, навигация, сравнение с моделями | Частично |
| Домены (обзор + 6 страниц) | SD §3.1–3.6, §4–5 | функция, определение, принцип, критерий завершения, соответствие реальности, типы ошибок; кейсы: невидимая горилла, Вальд, Земмельвейс, Гаванде, «Челленджер» | **Да**, с поправкой Д2/Д4 |
| Каталог ошибок (обзор + 5 типов + карточки) | AO (типы 1, 3, 4, 5); DV (тип 2) | определения, механизмы, диагностические вопросы | **Да — для формулировок;** коды и счёт брать с сайта (158) |
| Каталог парадоксов (обзор + 3 класса + 46 карточек) | PD целиком; T19 §5, §9; TS §4.1 | доменный разбор 10 центральных парадоксов; полная классификация | **Да**, с заменой dissolution |
| Тождество (кейс Тесея) | PD §4.1.2 | четыре критерия тождества | Частично: в PD четвёртый критерий legal/social, в коде `conceptual_same` — сверить |
| Эпистемология (обзор) | SD §3.1 (данные → информация → качества → характеристики), §8.2; T19 §12.2 (record) | — | Минимально |
| Интуиция | AO §6.2 (Trust Your Gut: когда верно, когда ошибка); SD §2.2 | — | Минимально |
| Правда и истина · Объективность и субъективность | SD §3.3 (Principle of Objectivity), §3.5 (Honesty of Inference), §5.1 (“structural alignment”) | — | **Нет:** пары правда/истина в статьях нет |
| Этика · Этический Кодекс · Устав · Путь Мудрости · Социальные Системы · Философия · Вопрос · «Чего нет, и быть не может» | — | — | **Опоры нет:** переводить с нуля по глоссарию |

Замечание по источникам: Том «Математика» ссылается на десятую статью — Horsocrates, *The E/R/R
Framework: Structure, Resolution, and the Diagnosis of Paradoxes* (April 2026); в папке
`Книги/Статьи` её нет. Если она существует, это ещё одна английская опора для «Теории Систем».

---

### 6. Расхождения, которые переводчик должен держать в голове

1. **Void → Source** (T19, FD и файлы `VoidLogic*.v` против канона и кода `PosSource`).
2. **«not dualism» → «дуализм начал»** (T19 §12.1, §12.6 против МП-45).
3. **L3:** в статьях «derived» (TS, PM); канон — бинарность (теорема) + тотальность («режим счёта
   о “сейчас”»).
4. **Статус L5:** в T18 — «law of structure itself»; в T19 — «the meta-law»; на сайте — второй
   мета-закон.
5. **P1–P4:** в PM свой набор (Wholeness, Complementarity, Hierarchy, Process).
6. **Порядок триады:** ярлык E/R/R и «(Elements → Roles → Rules)» в Томе «Математика» против канона
   R → R → E; в Этике, шаге 4, вопросы что/как/почему переставлены против ТС.
7. **Dissolution** (PD; обзоры АР и «Каталога парадоксов» на сайте) против правила 4 канона.
8. **Домены:** принцип Д2 (Infinite Questions → Корня), принцип Д4 (Presence → узловой).
9. **Каталог ошибок:** 150 → 158; коды подтипов и имена групп 1.A/1.B, 3.x, 4.1.x расходятся.
10. **Нумерация серии:** SD и AO обе подписаны «Article 4» (по тексту AO статья SD — третья).
    Заглавие T19 цитируется в трёх вариантах: “…Sequence and Hierarchy in the Structure of
    Reasoning” (T18, SD, AO, DV, PD), “…in the Structure of Logic” (TS), фактическое —
    “…Sequence, Hierarchy, and Preservation in the Structure of Logic” (v2). Годы: в TS все ссылки
    помечены 2025, в самих статьях — 2026.
11. **Имя автора:** Horsocrates / Horsokrates.
12. **Внутри сайта:** «Философская Гильдия» / «Гильдия Философов»; три формулы мудрости; в Уставе
    истина определена формулой правды; «мета-система» / «метасистема»; «форма» в двух
    противоположных смыслах (Логика ↔ элемент в роли). Комментарий кода «SLight: the first
    generated system» отстаёт от канона «Свет — проявленность как таковая».

---

### 7. Решения, нужные от автора (ответ по номерам)

1. **Правда / истина:** truth / exact truth (рекомендация) · truth / verity · pravda / istina (§3.1).
2. **Разум · ум · ментал:** Intellect · wit · the Mental (рекомендация) или Reason / Nous · acumen ·
   mind-stuff (§3.4, 3.5).
3. **Правота и правильность:** being right + right/wrong (рекомендация) или rightness +
   correct/incorrect (§3.2).
4. **Ярлык E/R/R:** в прозе “Rules–Roles–Elements triad”, E/R/R — только в «Формализации»
   (рекомендация); или оставить E/R/R как имя собственное (§2.18).
5. **Растворение парадоксов:** в новой прозе “the paradox does not form / is ill-formed”,
   dissolution — только как ссылка на PD (рекомендация); или сохранить dissolution как термин
   (§2.12). Если выбрано первое, стоит выправить и русские обзоры АР и «Каталога парадоксов».
6. Второстепенные: дуализм начал (§2.3) · открытая/закрытая система (§2.6) · Принцип Корня (§2.16) ·
   не-правда = non-truth (§2.11) · «Вера в Мудрость» (§2.15) · форма в смысле ТС (§3.6) ·
   знание-о в коде (“that”) (§2.10).
