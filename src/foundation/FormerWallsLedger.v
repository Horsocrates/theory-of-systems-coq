(** * FormerWallsLedger.v — СВОД-реестр «бывших стен»: каждая мнимая завершённая бесконечность = артефакт.

   Параллель к ZFCAxiomLedger.v.  Это СИНТЕЗ/КЛАССИФИКАЦИЯ (НЕ новая теорема): сводит откат трёх «высоких»
   теорем теории множеств в один аудируемый вердикт.  GENUINE-содержание (0-ax свидетели Element/role-
   стороны) живёт В ОТДЕЛЬНЫХ ФАЙЛАХ ПО МЕСТАМ — здесь они только цитируются:

     -- foundation/PowersetRoleType.v      : powerset_card (|P(l)|=2^|l|), cantor_bool_seq (диагональ);
     -- foundation/FiniteGameDeterminacy.v : finite_game_determined (обратная индукция, без башни);
     -- foundation/FiniteWqoPigeonhole.v   : bool_pigeonhole3 (конечное ядро wqo);
     -- направление «Процессная иерархия» (подъём двух «стен» к процессам, ступени 1–5):
        ProcessHierarchyCore (восходящая башня роль-типов), HierarchyDepthLadder (глубина = рунг
        всеведения), DeterminacyAscent (детерминированность: конечный рунг 0-ax + открытый = LPO),
        WqoProcessDecidable (nat-wqo + ℕ-измеримое замыкание + минимально-плохой выбор как процесс),
        ProcessHierarchySynthesis (свод).

   ★ ВЕРДИКТ.  Из трёх классических «стен» ни одна не есть подлинный P4-запрет: completed-P(N)
     откатывается к достигнутой роли/операции (ReachedFreely); полный Крускал и борелевская
     детерминированность — ЧАСТИЧНО ОТКАЧЕНЫ (PartiallyReached): их НИЖНИЕ рунги построены КАК
     ПРОЦЕССЫ (направление «Процессная иерархия»: nat-wqo + ℕ-измеримое замыкание + метод-как-процесс;
     конечная детерминированность 0-ax + открытый рунг = LPO), а ПОЛНЫЕ формы — consistency-strength
     ГОРИЗОНТ-ПОДЪЁМ, локализованный рунгом, без противоречия.  Единственный подлинный запрещённый
     объект — сама завершённая актуальная бесконечность (WCompletedInfinity), и это ОНТОЛОГИЧЕСКИЙ
     выбор P4, а не недостижимость.

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  Мы НЕ доказываем ПОЛНЫХ Крускала/Бореля — их ПОЛНЫЕ формы
   остаются ГОРИЗОНТОМ-ПОДЪЁМОМ (consistency-strength); ЧАСТИЧНЫЙ откат (нижние рунги как процессы)
   построен в направлении «Процессная иерархия» (ступени 1–5, цитаты выше).  Genuine — консолидация
   отката + наблюдение «ровно завершённая бесконечность = запрет»; конкретные свидетели — в файлах выше;
   вердикты опираются на уже доказанные 0-ax/classic результаты (диагональ, ординалы-процессы,
   wqo_nat_le + dc_chain, обратная индукция + LPO-рунг — цитаты).

   Elements: перечисления Wall/Status/Rollback.
   Roles:    «стена» = роль-требование; вердикт = роль (достигнуто/частично/не-привлечено/запрещено).
   Rules:    status; ровно WCompletedInfinity = ForbiddenObject; три стены откатываются (одна свободно, две частично).

   STATUS: 4 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Bool.

(* ===================================================================== *)
(*  Реестр-вердикт «бывших стен» (синтез/классификация)                    *)
(* ===================================================================== *)

Inductive Wall :=
  | WPowersetObject       (* завершённый P(N) как готовый объект *)
  | WMinimalBadSequence   (* полный Крускал через мин.-плохую последовательность *)
  | WBorelTower           (* борелевская детерминированность через башню степеней *)
  | WCompletedInfinity.   (* сама завершённая актуальная бесконечность *)

Inductive Status :=
  | ReachedFreely     (* откат к достигнутой операции/роли + конкретный 0-ax/classic свидетель *)
  | PartiallyReached  (* нижние рунги построены КАК ПРОЦЕССЫ (0-ax/classic); полная форма = горизонт-подъём *)
  | NotYetBuilt       (* процессная форма не привлечена — открыто, без противоречия *)
  | ForbiddenObject   (* завершённый объект, несовместимый с P4 *) .

Definition status (w : Wall) : Status :=
  match w with
  | WPowersetObject     => ReachedFreely   (* PowersetRoleType: powerset_card + cantor_bool_seq *)
  | WMinimalBadSequence => PartiallyReached  (* WqoProcessDecidable: nat-wqo + ℕ-измеримое замыкание + метод-как-процесс (0-ax); общий Крускал — горизонт *)
  | WBorelTower         => PartiallyReached  (* DeterminacyAscent: конечный рунг (0-ax) + открытый = LPO; полный Борель — consistency-strength горизонт *)
  | WCompletedInfinity  => ForbiddenObject
  end.

Definition forbidden (s : Status) : bool :=
  match s with ForbiddenObject => true | _ => false end.

(** Ровно одна «стена» — подлинный запрет: завершённая бесконечность. Остальные откатываются. *)
Theorem only_completed_infinity_is_a_wall :
  forall w, forbidden (status w) = true <-> w = WCompletedInfinity.
Proof. destruct w; split; intro H; first [reflexivity | discriminate]. Qed.

(** Три классические «стены» НЕ суть запрещённые объекты: одна достигнута свободно, две — ЧАСТИЧНО
    (нижние рунги построены как процессы; полные формы — горизонт-подъём, не противоречие). *)
Theorem high_walls_dissolve :
  status WPowersetObject = ReachedFreely /\
  status WMinimalBadSequence = PartiallyReached /\
  status WBorelTower = PartiallyReached.
Proof. repeat split. Qed.

(* ===================================================================== *)
(*  Демонстрация против ZFC: завершённый объект нужен ZFC, не нам           *)
(* ===================================================================== *)

(** Классически каждая «стена» постулирует завершённый объект. *)
Definition zfc_posits_completed_object (w : Wall) : bool := true.

(** В ToS завершённый объект нужен ТОЛЬКО самой бесконечности; содержание трёх «стен» достигается без
    него (см. PowersetRoleType / FiniteGameDeterminacy / FiniteWqoPigeonhole). *)
Definition tos_needs_completed_object (w : Wall) : bool :=
  match w with WCompletedInfinity => true | _ => false end.

Theorem tos_reaches_content_without_completed_object :
  forall w, w <> WCompletedInfinity ->
    zfc_posits_completed_object w = true /\ tos_needs_completed_object w = false.
Proof.
  intros w Hw. split.
  - reflexivity.
  - destruct w; try reflexivity. exfalso; apply Hw; reflexivity.
Qed.

(** Капстоун: «бывшие стены» — артефакты ZFC-упаковки. Для каждой (кроме самой бесконечности) ZFC
    постулирует завершённый объект, а ToS достигает содержания без него; единственный подлинный
    запрет — завершённая актуальная бесконечность (выбор P4). *)
Theorem former_walls_are_artifacts :
  (forall w, w <> WCompletedInfinity ->
     zfc_posits_completed_object w = true /\ tos_needs_completed_object w = false)
  /\ (forall w, forbidden (status w) = true <-> w = WCompletedInfinity).
Proof.
  split.
  - exact tos_reaches_content_without_completed_object.
  - exact only_completed_infinity_is_a_wall.
Qed.
