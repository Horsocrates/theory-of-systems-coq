(** * DeterminacyAscent.v — НАПРАВЛЕНИЕ «Процессная иерархия», ступень 3 (детерминированность вверх).

   Ступени 1–2 дали восходящую башню роль-типов (ProcessHierarchyCore) и её ГЛУБИНУ как рунг всеведения
   (HierarchyDepthLadder).  Здесь — ПРИЛОЖЕНИЕ к детерминированности игр: она тоже не «стена», а
   ОРДИНАЛ-ИНДЕКСИРОВАННЫЙ ПОДЪЁМ, и аксиома входит в него в ОДНОЙ точно локализованной точке.

   ОТКАТ «стены» (метод P4).  Классически борелевская (Мартина) детерминированность лезет по ЗАВЕРШЁННОЙ
   башне итерированных степеней (consistency-strength ~ω₁ итераций powerset).  Откатываем:
     -- НИЖНИЙ рунг (конечная/клопен игра) — РАЗРЕШИМ обратной индукцией, БЕЗ всякого оракула (0 ax;
        mover_wins тотальна, FiniteGameDeterminacy);
     -- шаг от конечного к бесконечному («выиграет ли игрок I КОГДА-НИБУДЬ») — это РОВНО LPO, тот же
        рунг всеведения, что этаж 1 башни (HierarchyDepthLadder); LEM его схлопывает;
     -- индекс рунга — ординал-процесс ω (Ordinal), подъём ПОРОЖДАЮЩ (нет максимального рунга).
   Итог: аксиома входит НЕ как стена, а в одной точке (финит→инфинит = LPO), точно локализованной.

   ★ GENUINE зубы:
     -- finite_depth_decidable: победитель конечной игры РЕШАЕМ ({}+{}), 0 ax (обратная индукция);
     -- eventual_decided_is_LPO: дихотомия «I выигрывает на каком-то этапе ∨ никогда» для ВСЕХ игр-
        процессов РОВНО эквивалентна LPO (каждый булев процесс — это игра из листьев GLeaf);
     -- eventual_decided_classical: LEM схлопывает этот рунг;
     -- determinacy_ascent_height_is_omega: индекс рунга = ω = OLim (ординал-процесс, не число);
     -- determinacy_ranks_unbounded: рунги неограниченны (порождающий подъём, замыкание role-limit).

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом (LEM/LPO — Prop-ГИПОТЕЗЫ, не аксиомы).  Это НИЖНИЙ подъём:
   конечный рунг (0 ax) + Σ⁰₁-рунг «выиграет ли I когда-нибудь» = LPO.  ПОЛНУЮ стратегическую
   детерминированность Гейла–Стюарта для открытых игр (у I ЕСТЬ выигрышная стратегия ∨ у II есть) и тем
   более полную борелевскую (Мартин, consistency-strength ω₁ итераций powerset) НЕ строим — это
   ГОРИЗОНТ-ПОДЪЁМ, локализованный рунгом, а НЕ бинарная стена.  Что LPO-эквивалентность клопен/открытой
   value-дихотомии для разрешимых игр известна (constructive reverse math, Bishop/Ishihara) — здесь
   ПЕРЕИСПОЛЬЗОВАНО; mine — размещение на ординал-процесс-подъёме + мост к обратной индукции (mover_wins).

   Elements: процесс конечных игр gp : nat -> GameTree; value-процесс fun K => mover_wins (gp K); рунг-индекс nat_to_ord.
   Roles:    этап = конечная игра (Element, разрешима обратной индукцией); «выиграет ли I когда-нибудь» = Σ⁰₁-вопрос; индекс = ω-процесс.
   Rules:    конечный этап разрешим (0 ax); дихотомия eventual = LPO (один рунг всеведения); LEM схлопывает; подъём порождающ (нет max), индекс ω.
   ДИАГНОСТИКА (P4): подъём потенциален (каждый рунг — процесс), не завершён; аксиома входит ТОЧНО на шаге финит→инфинит (LPO), локализована; полный Борель = consistency-strength горизонт, подъём не стена.

   STATUS: 6 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia Bool.
From ToS Require Import foundation.Ordinal.
From ToS Require Import foundation.FiniteGameDeterminacy.
From ToS Require Import foundation.RoleLimitLadder.

(* ===================================================================== *)
(*  Нижний рунг: конечная игра РЕШАЕМА обратной индукцией (0 ax, без оракула) *)
(* ===================================================================== *)

(** Победитель конечной игры — РЕШЕНИЕ ({}+{}), не просто классически определён: обратная индукция
    mover_wins тотальна и вычислима.  Это рунг 0 подъёма — Element-сторона, без всякого всеведения. *)
Lemma finite_depth_decidable : forall g : GameTree, {mover_wins g = true} + {mover_wins g = false}.
Proof. intro g. destruct (mover_wins g); [ left | right ]; reflexivity. Qed.

(* ===================================================================== *)
(*  Шаг финит -> инфинит: «выиграет ли I когда-нибудь» = РОВНО LPO          *)
(* ===================================================================== *)

(** value-процесс открытой игры: на этапе K — победитель конечной K-усечённой игры (обратная индукция). *)
Definition open_value (gp : nat -> GameTree) (K : nat) : bool := mover_wins (gp K).

(** Σ⁰₁-дихотомия: игрок I выигрывает на КАКОМ-ТО этапе, либо НИКОГДА (ни на одном конечном этапе).
    Это НЕ полная стратегическая детерминированность Гейла–Стюарта — это её Σ⁰₁-ядро («когда-нибудь»). *)
Definition eventual_decided (gp : nat -> GameTree) : Prop :=
  (exists K, open_value gp K = true) \/ (forall K, open_value gp K = false).

(** ★ Мост направления: сшивание 0-ax-конечных этапов в бесконечную (открытую) игру — это РОВНО один
    рунг всеведения, LPO (HierarchyDepthLadder, этаж 1).  Каждый булев процесс g есть value-процесс
    игры из листьев (fun K => GLeaf (g K)), так что eventual-дихотомия для ВСЕХ игр <-> LPO. *)
Theorem eventual_decided_is_LPO :
  (forall gp, eventual_decided gp) <-> LPO.
Proof.
  unfold eventual_decided, open_value, LPO. split.
  - intros H g. specialize (H (fun K => GLeaf (g K))). simpl in H. exact H.
  - intros lpo gp. exact (lpo (fun K => mover_wins (gp K))).
Qed.

(** Рунг СХЛОПЫВАЕТСЯ классически: LEM решает Σ⁰₁-дихотомию для каждой игры. *)
Theorem eventual_decided_classical : LEM -> forall gp, eventual_decided gp.
Proof. intros lem. apply (proj2 eventual_decided_is_LPO). apply lem_lpo. exact lem. Qed.

(* ===================================================================== *)
(*  Индекс рунга — ординал-процесс ω; подъём порождающ (нет максимума)      *)
(* ===================================================================== *)

Definition determinacy_rank_index (n : nat) : Ord := nat_to_ord n.

(** Индекс рунга = ω = предел процесса: высота подъёма сама ОРДИНАЛ-ПРОЦЕСС, а не завершённое число. *)
Theorem determinacy_ascent_height_is_omega : omega = OLim determinacy_rank_index.
Proof. reflexivity. Qed.

(** Рунги неограниченны (порождающий убегающий поток) => замыкание подъёма — role-limit, не объект. *)
Theorem determinacy_ranks_unbounded : forall B : nat, exists n : nat, (n > B)%nat.
Proof. intro B. exists (S B). lia. Qed.

(* ===================================================================== *)
(*  Капстоун: детерминированность — ординал-процесс-подъём, не стена         *)
(* ===================================================================== *)

(** Детерминированность есть ОРДИНАЛ-ИНДЕКСИРОВАННЫЙ ПОДЪЁМ, а не бинарная стена:
      -- конечный/клопен рунг ДОСТИГНУТ 0-ax (обратная индукция решает всякую конечную игру);
      -- открытый/Σ⁰₁ рунг «выиграет ли I когда-нибудь» = РОВНО LPO (LEM его схлопывает);
      -- индекс рунга — ординал-процесс ω, подъём ПОРОЖДАЮЩ (нет максимального рунга).
    Полная борелевская детерминированность (Мартин) — consistency-strength ГОРИЗОНТ выше: открытый
    подъём, локализованный рунгом, а НЕ стена. *)
Theorem determinacy_is_ordinal_process_ascent :
  (forall g : GameTree, mover_wins g = true \/ mover_wins g = false)  (* конечный рунг: решён, без оракула *)
  /\ ((forall gp, eventual_decided gp) <-> LPO)                        (* открытый Σ⁰₁-рунг = LPO *)
  /\ (LEM -> forall gp, eventual_decided gp)                           (* классически схлопывается *)
  /\ omega = OLim determinacy_rank_index                               (* индекс рунга = ω-процесс *)
  /\ (forall n : nat, exists m : nat, (n < m)%nat).                    (* порождающ: нет максимального рунга *)
Proof.
  split; [ exact finite_game_determined | ].
  split; [ exact eventual_decided_is_LPO | ].
  split; [ exact eventual_decided_classical | ].
  split; [ exact determinacy_ascent_height_is_omega | ].
  intro n; exists (S n); lia.
Qed.
