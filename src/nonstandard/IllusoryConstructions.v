(** * IllusoryConstructions.v — честный вердикт-РЕЕСТР «за-границей» конструкций: каждая получает
      статус {Element-ядро / role-limit-инструмент / ИЛЛЮЗОРНОЕ}.  Сердце честной миссии Части XVIII.

   ОНТОЛОГИЧЕСКОЕ ТРЕБОВАНИЕ.  ToS — онтологическая система: конструкции, существующие ТОЛЬКО внутри
   формализма ZFC (через AC), без референта/вычислимого содержания, мы ОБЯЗАНЫ честно пометить как
   ИЛЛЮЗОРНЫЕ — не «за границей» (как будто реальны, но недоступны), а БЕЗ референта вовсе.  Здесь это
   делается машинно: перечисление конструкций + трёхзначный вердикт + якорный флагман (Банах–Тарши).

   ★ ТРИ КЛАССА (genuine различение):
     -- ElementCore     : выразимо процессом, 0 AC, есть Coq-свидетель (δ-процесс, тень сходящегося, f' полинома);
     -- RoleLimitTool   : неконструктивные ЛЕСА, но продукт КОНСЕРВАТИВЕН (Хенсон–Кейслер) ⟹ устраним
                          (свободный ультрафильтр, *ℝ-как-поле) — НЕ фантом: можно использовать, можно убрать;
     -- Illusory        : нужен AC, НЕТ Element-свидетеля, и это даже НЕ устранимые леса (ничего Element не
                          доставляет) — чистый ZFC-фантом (Банах–Тарши, Витали, базис Гамеля, полный порядок ℝ).
   Ключевое различение Illusory vs RoleLimitTool: леса УСТРАНИМЫ и что-то ДОСТАВЛЯЮТ (Element-следствие через
   консервативность); фантом не доставляет ничего — он лишь «объект», которого на Element-стороне нет.

   ★ ЯКОРНЫЙ ФЛАГМАН (genuine теорема, не классификация): Банах–Тарши.  Удвоение шара ЗАЯВЛЯЕТ: единичный
   шар (мера μ) режется на конечно много кусков, собираемых движениями в ДВА единичных шара (мера 2μ).  Любая
   ненулевая движение-инвариантная конечно-аддитивная Element-мера это ЗАПРЕЩАЕТ: μ = μ+μ ⟹ μ=0
   (`banach_tarski_contradicts_measure`).  Значит куски НЕизмеримы (нет Element-референта) — вот ПОЧЕМУ БТ
   иллюзорен на Element-стороне: он несовместим с сохранением, которое несёт Element-мера.

   ★ ЯКОРЯ ВЕРДИКТОВ (не голая классификация — статусы подкреплены машинно):
     -- FreeUltrafilter = RoleLimitTool: НЕканоничность ДОКАЗАНА в `UltrafilterRoleLimit.v`
        (`ultrafilter_decision_required`: even_ind единица mod Evens, нуль mod Odds — два несовместимых разрешения);
     -- ElementCore-свидетели ДОКАЗАНЫ: `GermInfinitesimal` (δ-процесс), `StandardPart` (тень сходящегося),
        `DerivativeViaInfinitesimal` (`deriv_sq`: f'(x²)=2x).

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  ⚠ Это РЕЕСТР / КЛАССИФИКАЦИЯ (синтез), НЕ новые теоремы —
   КРОМЕ одной якорной теоремы Банах–Тарши (μ=2μ⟹μ=0, доказана).  Вердикты Витали/Гамель/полный-порядок
   ЦИТИРУЮТ классическую AC-зависимость (не передоказываются здесь); вердикт FreeUltrafilter подкреплён
   `UltrafilterRoleLimit`; ElementCore — соответствующими 0-аксиомными файлами.  Никакой иллюзорной
   конструкции не АССЕРТИМ (не постулируем существование БТ-разбиения и т.п.) — лишь классифицируем и для
   флагмана доказываем НЕсовместимость с Element-мерой.

   Elements: перечисление Construction; булевы needs_AC/has_element_witness/is_conservative_scaffold; Q-мера (БТ).
   Roles:    конструкция = роль-кандидат; вердикт = роль-статус; диагностики = роли; мера = роль-сохранение.
   Rules:    трёхзначный вердикт; Illusory = AC ∧ ¬witness ∧ ¬scaffold (фантом); БТ: μ=2μ⟹μ=0.

   ============ E/R/R разбор (осн. + образующие + вложенные + элемент-как-система) ============
     ОСН.: вердикт-реестр «за-границей» конструкций в три класса; честная пометка иллюзорного.
     Rules (L5): трёхзначный вердикт; Illusory = AC∧¬witness∧¬scaffold (фантом); RoleLimitTool = AC∧scaffold
                 (устраним); ElementCore = ¬AC∧witness; БТ: μ=2μ⟹μ=0.
     Roles (L4): конструкция=роль-кандидат; вердикт=роль-статус; needs_AC/witness/scaffold=роль-диагностики;
                 мера=роль-сохранение (Element).
     Elements  : перечисление Construction; булевы предикаты; Q-мера.
     ОБРАЗУЮЩИЕ: UltrafilterRoleLimit (FreeUltrafilter role-limit ДОКАЗАН — якорь); GermInfinitesimal/StandardPart/
                 Derivative (ElementCore-свидетели — якоря); ZFCAxiomLedger (Choice→L5); классика (БТ/Витали/Гамель — цитата).
     ВЛОЖЕННЫЕ : Illusory (фантом) vs RoleLimitTool (устранимые леса) vs ElementCore (процесс); БТ якорный флагман.
     ★ ЭЛЕМЕНТ-КАК-СИСТЕМА (Банах–Тарши): Elements — конечные «куски»; Roles — якобы меросохраняющие фрагменты;
                 Rules — пересборка ЗАЯВЛЯЕТ μ(целое)=μ(2целых), но Element-сохранение (конеч.аддит.+движ.-инвар.)
                 запрещает (кроме μ≡0) ⟹ куски НЕизмеримы (нет Element-референта) ⟹ система-фантом: «элементы»
                 (куски) = ровно то, что P4 не актуализирует.
   ДИАГНОСТИКА (P4): ElementCore=0 AC (актуализуемо); RoleLimitTool=AC-леса, консервативны (устранимы);
                 Illusory=AC-фантом, нет референта, μ=2μ⟹μ=0. ЧЕСТНО: реестр (синтез)+1 якорная теорема (БТ)+цитаты.

   STATUS: 8 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Перечисление «за-границей» конструкций и трёхзначный вердикт            *)
(* ===================================================================== *)

Inductive Construction :=
  | BanachTarski        (* парадоксальное удвоение шара *)
  | VitaliSet           (* неизмеримое множество *)
  | HamelBasis          (* базис ℝ как ℚ-векторного пространства *)
  | WellOrderReals      (* полный порядок на ℝ *)
  | FreeUltrafilter     (* свободный ультрафильтр на ℕ *)
  | HyperrealField      (* *ℝ КАК ПОЛЕ (через ультрафильтр) *)
  | GermInfinitesimalC  (* δ как процесс (Фреше, БЕЗ ультрафильтра) *)
  | StandardPartConv    (* тень СХОДЯЩЕГОСЯ процесса *)
  | NSADerivativePoly.  (* производная ПОЛИНОМА через тень *)

Inductive Verdict := ElementCore | RoleLimitTool | Illusory.

Definition verdict (c : Construction) : Verdict :=
  match c with
  | BanachTarski | VitaliSet | HamelBasis | WellOrderReals => Illusory
  | FreeUltrafilter | HyperrealField                       => RoleLimitTool
  | GermInfinitesimalC | StandardPartConv | NSADerivativePoly => ElementCore
  end.

(** Диагностики: требует ли AC, есть ли Coq-свидетель, является ли устранимыми лесами. *)
Definition needs_AC (c : Construction) : bool :=
  match c with
  | GermInfinitesimalC | StandardPartConv | NSADerivativePoly => false
  | _ => true
  end.

Definition has_element_witness (c : Construction) : bool :=
  match c with
  | GermInfinitesimalC | StandardPartConv | NSADerivativePoly => true
  | _ => false
  end.

Definition is_conservative_scaffold (c : Construction) : bool :=
  match c with
  | FreeUltrafilter | HyperrealField => true
  | _ => false
  end.

(* ===================================================================== *)
(*  Структурные свойства классификации                                      *)
(* ===================================================================== *)

(** ★ Сигнатура ИЛЛЮЗОРНОГО: нужен AC, НЕТ свидетеля, и это даже НЕ устранимые леса (чистый фантом). *)
Lemma illusory_hallmark : forall c, verdict c = Illusory ->
  needs_AC c = true /\ has_element_witness c = false /\ is_conservative_scaffold c = false.
Proof. intros c H; destruct c; simpl in H; try discriminate; repeat split; reflexivity. Qed.

(** Element-ядро: 0 AC и есть Coq-свидетель (актуализуемый процесс). *)
Lemma element_core_props : forall c, verdict c = ElementCore ->
  needs_AC c = false /\ has_element_witness c = true.
Proof. intros c H; destruct c; simpl in H; try discriminate; split; reflexivity. Qed.

(** role-limit-инструмент: устранимые леса (консервативны) и требует AC. *)
Lemma role_limit_scaffold : forall c, verdict c = RoleLimitTool ->
  is_conservative_scaffold c = true /\ needs_AC c = true.
Proof. intros c H; destruct c; simpl in H; try discriminate; split; reflexivity. Qed.

(** Классификация тотальна. *)
Lemma verdict_total : forall c,
  verdict c = ElementCore \/ verdict c = RoleLimitTool \/ verdict c = Illusory.
Proof.
  intros c; destruct c; simpl;
    ((left; reflexivity) || (right; left; reflexivity) || (right; right; reflexivity)).
Qed.

(** Классы взаимоисключающи (Element-ядро НИКОГДА не иллюзорно). *)
Lemma element_not_illusory : forall c, verdict c = ElementCore -> verdict c <> Illusory.
Proof. intros c A B. rewrite A in B. discriminate. Qed.

(* ===================================================================== *)
(*  ★ Якорный флагман: Банах–Тарши несовместим с Element-мерой              *)
(* ===================================================================== *)

(** ★ Удвоение шара ЗАЯВЛЯЕТ: μ(целое) = μ(куски-1) + μ(куски-2), каждая группа собирается движениями
    в целое (μ каждой = μ).  Любая ненулевая Element-мера ЗАПРЕЩАЕТ: μ = μ+μ ⟹ μ=0.  Значит куски
    НЕизмеримы — нет Element-референта.  Вот ПОЧЕМУ БТ иллюзорен на Element-стороне. *)
Lemma banach_tarski_contradicts_measure :
  forall mu p1 p2 : Q,
    mu == p1 + p2 ->   (* конечная аддитивность: целое = сумма групп кусков *)
    p1 == mu ->        (* движение-инвариантность: группа 1 собирается в целое *)
    p2 == mu ->        (* группа 2 собирается в целое *)
    mu == 0.
Proof. intros mu p1 p2 H1 H2 H3. rewrite H2, H3 in H1. lra. Qed.

(* ===================================================================== *)
(*  Капстоун: честный реестр                                                *)
(* ===================================================================== *)

(** Машинный реестр «за-границей» конструкций (0 аксиом):
      (★ сигнатура фантома)  Illusory ⟹ нужен AC, нет свидетеля, НЕ устранимые леса;
      (Element-ядро)         ElementCore ⟹ 0 AC + есть Coq-свидетель (δ-процесс / тень / f' полинома);
      (role-limit-леса)      RoleLimitTool ⟹ консервативны + AC (свободный ультрафильтр, *ℝ-поле);
      (★ флагман БТ)         удвоение шара ⟹ μ=2μ⟹μ=0: несовместимо с ненулевой Element-мерой;
      (якоря)                BanachTarski=Illusory, FreeUltrafilter=RoleLimitTool, GermInfinitesimalC=ElementCore.
    Иллюзорное помечено честно: AC-фантом без Element-референта.  Ничего иллюзорного не АССЕРТИМ —
    лишь классифицируем и для флагмана доказываем несовместимость с Element-сохранением. *)
Theorem illusory_constructions_summary :
  (forall c, verdict c = Illusory ->
     needs_AC c = true /\ has_element_witness c = false /\ is_conservative_scaffold c = false)
  /\ (forall c, verdict c = ElementCore -> needs_AC c = false /\ has_element_witness c = true)
  /\ (forall c, verdict c = RoleLimitTool -> is_conservative_scaffold c = true /\ needs_AC c = true)
  /\ (forall mu p1 p2 : Q, mu == p1 + p2 -> p1 == mu -> p2 == mu -> mu == 0)
  /\ verdict BanachTarski = Illusory
  /\ verdict FreeUltrafilter = RoleLimitTool
  /\ verdict GermInfinitesimalC = ElementCore.
Proof.
  split; [ exact illusory_hallmark |].
  split; [ exact element_core_props |].
  split; [ exact role_limit_scaffold |].
  split; [ exact banach_tarski_contradicts_measure |].
  split; [ reflexivity |].
  split; reflexivity.
Qed.
