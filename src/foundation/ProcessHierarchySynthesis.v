(** * ProcessHierarchySynthesis.v — НАПРАВЛЕНИЕ «Процессная иерархия», ступень 5 (синтез).

   Свод направления.  Ступени 1–4 построили role-limit-сторону границы финитизации как ЕДИНЫЙ
   ОРДИНАЛ-ПРОЦЕСС-ПОДЪЁМ, а не плоскость и не «стену».  Здесь — синтез: что именно СШИВАЕТ ступени в
   одну иерархию, и обновление реестра «бывших стен».

   ★ ДВЕ НИТИ, сшивающие ступени (genuine-теоремы синтеза, не пересказ):
     -- ЕДИНЫЙ ИНДЕКС-ПОДЪЁМ.  И башня роль-типов (ст.1), и подъём детерминированности (ст.3)
        индексированы ОДНИМ ординал-процессом ω = OLim (foundation/Ordinal.v): высота — процесс, не
        завершённое число.  Порождающность общая: нет максимального этажа/рунга.
     -- ОДИН РУНГ ВСЕВЕДЕНИЯ ПОВТОРЯЕТСЯ.  Этаж 1 башни (решение Level 1 = nat->bool, ст.2) и открытый
        рунг детерминированности («выиграет ли I когда-нибудь», ст.3) — ОДИН И ТОТ ЖЕ рунг LPO; отсюда
        level1_equiv_open_determinacy: они ЭКВИВАЛЕНТНЫ.  И оба КОНСТРУКТИВНЫ: LEM схлопывает (виден лишь
        через P4).  То же LPO — это и Σ⁰₁-«край» wqo-метода над разрешимым (ст.4), и нижний рунг лестницы
        всеведения (RoleLimitLadder): иерархия едина по рунгам.

   ★ 0-AX БАЗА ПОДЪЁМА.  Нижние рунги достигнуты БЕЗ оракула: конечная детерминированность — обратной
     индукцией (mover_wins), nat-wqo — фундированным спуском (wqo_nat_le); оба 0-ax процессы.  Аксиома
     (LPO/classic) входит ВЫШЕ, в точно локализованных точках (финит→инфинит = LPO), а не как стена.

   ★ ОБНОВЛЕНИЕ РЕЕСТРА.  Две «бывшие стены» — минимально-плохая последовательность (Крускал) и
     борелевская башня — переведены NotYetBuilt -> PartiallyReached (walls_upgraded_by_direction):
     их нижние рунги построены как процессы; полные формы остаются consistency-strength ГОРИЗОНТОМ-
     ПОДЪЁМОМ.  Единственный подлинный P4-запрет — завершённая актуальная бесконечность (выбор, не стена).

   ФЛАГМАН-ПЕРЕОБРАМЛЕНИЕ: ИЕРАРХИЯ = ПРОЦЕСС — теоретико-множественный аналог ℝ=Коши-процесс,
   ℚ̄=башня, многообразие=процесс: восходящий ординал-процесс-подъём роль-типов, градуированный
   всеведением, с 0-ax базой и точно локализованной аксиомой, а НЕ завершённый объект и НЕ бинарная стена.

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом (LEM/LPO — Prop-гипотезы).  Синтез ЦИТИРУЕТ доказанные
   ступени 1–4 и сшивает их двумя нитями (единый ω-индекс + повторяющийся LPO-рунг) — это genuine
   placement/унификация, НЕ новые «высокие» теоремы.  ПОЛНЫЕ Крускал/Борель НЕ доказаны (горизонт-
   подъём, см. WqoProcessDecidable / DeterminacyAscent / FormerWallsLedger).

   Elements: ступени 1–4 как доказанные факты; индекс ω; рунг LPO; реестр стен.
   Roles:    ω = общий индекс-подъём; LPO = общий рунг (этаж 1 = открытая детерминированность); вердикт реестра = роль.
   Rules:    единый ω-индекс (ст.1=ст.3); level1 <-> открытая детерминированность (оба LPO); 0-ax база; реестр: две стены PartiallyReached.
   ДИАГНОСТИКА (P4): иерархия — один процесс-подъём (не объект, не стена); аксиома локализована (LPO выше 0-ax базы); полные формы — горизонт.

   STATUS: 3 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia Bool.
From ToS Require Import foundation.Ordinal.
From ToS Require Import foundation.ProcessHierarchyCore.
From ToS Require Import foundation.HierarchyDepthLadder.
From ToS Require Import foundation.DeterminacyAscent.
From ToS Require Import foundation.WqoProcessDecidable.
From ToS Require Import foundation.RoleLimitLadder.
From ToS Require Import foundation.FormerWallsLedger.
(* short names from transitively-required modules (not re-exported by the stage files): *)
From ToS Require Import foundation.FiniteGameDeterminacy.   (* GameTree, mover_wins, finite_game_determined *)
From ToS Require Import settheory.KruskalTree.              (* is_wqo, wqo_nat_le *)

(* ===================================================================== *)
(*  Нить 2: ОДИН рунг LPO — этаж 1 башни = открытый рунг детерминированности *)
(* ===================================================================== *)

(** ★ Синтез ст.2 <-> ст.3: решение этажа 1 башни роль-типов (decide_level1) ЭКВИВАЛЕНТНО открытой
    детерминированности (выиграет ли I когда-нибудь) — потому что ОБА суть один рунг всеведения LPO.
    Глубина иерархии и подъём детерминированности — одна и та же лестница рунгов. *)
Corollary level1_equiv_open_determinacy :
  decide_level1 <-> (forall gp, eventual_decided gp).
Proof.
  split; intro H.
  - apply eventual_decided_is_LPO. apply level1_decision_is_LPO. exact H.
  - apply level1_decision_is_LPO. apply eventual_decided_is_LPO. exact H.
Qed.

(* ===================================================================== *)
(*  Обновление реестра «бывших стен» направлением                          *)
(* ===================================================================== *)

(** Две «бывшие стены» переведены NotYetBuilt -> PartiallyReached: их нижние рунги построены
    как процессы (ст.3, ст.4); полные формы — consistency-strength горизонт-подъём. *)
Theorem walls_upgraded_by_direction :
  status WMinimalBadSequence = PartiallyReached /\ status WBorelTower = PartiallyReached.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  Капстоун синтеза: иерархия = процесс                                    *)
(* ===================================================================== *)

(** Процессная иерархия — ЕДИНЫЙ ординал-процесс-подъём, сшитый двумя нитями, с 0-ax базой и
    обновлённым реестром:
      (индекс)    ω = OLim — общий индекс башни (ст.1) и детерминированности (ст.3);
      (порожд.)   нет максимального этажа/рунга;
      (рунг LPO)  этаж 1 (ст.2) и открытая детерминированность (ст.3) — один рунг LPO;
      (констр.)   LEM схлопывает оба (виден лишь через P4);
      (0-ax база) конечная детерминированность (обратная индукция) + nat-wqo (фундир. спуск);
      (реестр)    две «стены» PartiallyReached; единственный запрет — завершённая бесконечность. *)
Theorem process_hierarchy_synthesis :
  (omega = OLim level_index /\ omega = OLim determinacy_rank_index)
  /\ (forall n : nat, exists m : nat, (n < m)%nat)
  /\ ((decide_level1 <-> LPO) /\ ((forall gp, eventual_decided gp) <-> LPO))
  /\ ((LEM -> decide_level1) /\ (LEM -> forall gp, eventual_decided gp))
  /\ ((forall g : GameTree, mover_wins g = true \/ mover_wins g = false) /\ is_wqo Nat.le)
  /\ (status WMinimalBadSequence = PartiallyReached
      /\ status WBorelTower = PartiallyReached
      /\ (forall w, forbidden (status w) = true <-> w = WCompletedInfinity)).
Proof.
  split; [ split; [ exact tower_height_is_limit_process | exact determinacy_ascent_height_is_omega ] | ].
  split; [ intro n; exists (S n); lia | ].
  split; [ split; [ exact level1_decision_is_LPO | exact eventual_decided_is_LPO ] | ].
  split; [ split; [ exact lem_decides_level1 | exact eventual_decided_classical ] | ].
  split; [ split; [ exact finite_game_determined | exact wqo_nat_le ] | ].
  split; [ reflexivity | ]. split; [ reflexivity | ]. exact only_completed_infinity_is_a_wall.
Qed.
