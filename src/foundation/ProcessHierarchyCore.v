(** * ProcessHierarchyCore.v — НАПРАВЛЕНИЕ «Процессная иерархия», ступень 1 (ядро).

   Тезис направления: role-limit-сторона границы финитизации — НЕ плоская и НЕ «стена», а
   ОРДИНАЛ-ИНДЕКСИРОВАННЫЙ ВОСХОДЯЩИЙ ПОДЪЁМ роль-типов.  Здесь — ядро: восходящая башня роль-типов,
   порождающая (нет максимального этажа), индексированная ординалом-процессом ω, чьё замыкание —
   role-limit (незавершимо), а каждый этаж достижим.

   КОНСТРУКЦИЯ.  Этаж n — роль-тип над предыдущим: Level 0 = nat, Level (S k) = Level k -> bool
   (предикаты над этажом k — та же роль ℕ->bool, поднятая на ярус).  Это процессная кумулятивная
   башня: каждый этаж — пространство процессов-решений над нижним.

   ★ GENUINE 0-ax зубы:
     -- cantor_level: НЕТ сюръекции Level n -> Level (S n) (диагональ на каждом этаже) => башня
        СТРОГО растёт, этаж за этажом (обобщает cantor_bool_seq: при n=0 это «нет перечислителя ℕ->bool»);
     -- no_maximal_level: над любым этажом есть строго больший => ПОРОЖДАЮЩАЯ структура, нет вершины
        (аналог no_maximal_rung у ℚ̄ и многообразия-процесса);
     -- tower_height_unbounded: высота башни — неограниченный монотонный поток => замыкание role-limit
        (дихотомия InterLevelCalculus: монот.+неогранич = role-limit);
     -- tower_height_is_limit_process: индекс высоты = ω = OLim (foundation/Ordinal.v), предел
        процесса — то есть высота башни сама есть ОРДИНАЛ-ПРОЦЕСС, а не завершённое число.

   ★ Образ P4.  Башня — потенциальна: каждый этаж конечно-конструируем (Element-сторона), но её
     ω-замыкание не есть завершённый Element-объект — оно достижимо лишь как процесс (точка базового
     роль-типа Level 1 = nat->bool ЕСТЬ процесс-нить).  Завершённой иерархии-объекта (классич. V_ω,
     борелевская/проективная башни) НЕ строим — это ZFC-упаковка (см. FormerWallsLedger).

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  Это ЯДРО направления (ступень 1): структура подъёма +
   его порождающность + ординал-процесс-индекс.  Применения (детерминированность вверх по башне, wqo
   как процесс) — следующие ступени (DeterminacyAscent, WqoProcessDecidable), НЕ здесь.  Полная
   борелевская/проективная башни — горизонты-подъёмы (consistency-strength), не объекты.

   Elements: этажи-роль-типы Level n (каждый конечно-конструируем на стадии); поток высоты nat->nat.
   Roles:    Level n = роль-тип над n-1; высота = ординал-процесс ω; диагональ = правило подъёма.
   Rules:    cantor_level (строгий подъём); no_maximal_level (нет вершины); unbounded => role-limit-замыкание.
   ДИАГНОСТИКА (P4): подъём порождающий и незавершим; ω-замыкание — процесс, не Element-объект.

   STATUS: 5 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia Bool.
From ToS Require Import foundation.Ordinal.

(* ===================================================================== *)
(*  Восходящая башня роль-типов: Level 0 = nat, Level (S k) = Level k -> bool *)
(* ===================================================================== *)

Fixpoint Level (n : nat) : Type :=
  match n with
  | O => nat
  | S k => Level k -> bool
  end.

(** Кантор на КАЖДОМ этаже: нет сюръекции Level n -> Level (S n).  Башня строго растёт.
    (При n=0: нет перечислителя ℕ -> (ℕ -> bool) — то самое ядро «несчётности».) *)
Theorem cantor_level :
  forall (n : nat) (f : Level n -> Level (S n)),
    exists g : Level (S n), forall x : Level n, g <> f x.
Proof.
  intros n f. exists (fun x : Level n => negb (f x x)). intros x Heq.
  apply (f_equal (fun h => h x)) in Heq. simpl in Heq.
  destruct (f x x); discriminate.
Qed.

(** Нет максимального этажа: над любым n есть строго больший m, не накрываемый сюръективно. *)
Theorem no_maximal_level :
  forall n : nat,
    exists m : nat, (n < m)%nat /\
      (forall f : Level n -> Level m, exists g : Level m, forall x : Level n, g <> f x).
Proof.
  intro n. exists (S n). split.
  - lia.
  - apply cantor_level.
Qed.

(* ===================================================================== *)
(*  Индекс высоты — ординал-процесс ω (foundation/Ordinal.v)               *)
(* ===================================================================== *)

Definition level_index (n : nat) : Ord := nat_to_ord n.

(** Высота башни = ω = предел процесса индексов: высота сама есть ОРДИНАЛ-ПРОЦЕСС, не число. *)
Theorem tower_height_is_limit_process : omega = OLim level_index.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Незамкнутость: высота — неограниченный поток => замыкание role-limit    *)
(* ===================================================================== *)

Definition tower_height_flow (n : nat) : nat := n.

(** Высота неограниченна (монотонный убегающий поток) => по дихотомии InterLevelCalculus
    (монот.+неогранич = role-limit) замыкание башни — role-limit, не Element-объект. *)
Theorem tower_height_unbounded :
  forall B : nat, exists n : nat, (tower_height_flow n > B)%nat.
Proof. intro B. exists (S B). unfold tower_height_flow. lia. Qed.

(* ===================================================================== *)
(*  Капстоун: порождающий ординал-индексированный подъём                    *)
(* ===================================================================== *)

(** Ядро направления: башня роль-типов СТРОГО восходит (Кантор на каждом этаже), ПОРОЖДАЮЩАЯ
    (нет вершины), индексирована ординалом-процессом ω, и её высота неограниченна (замыкание
    role-limit).  «Иерархия = процесс»: подъём потенциален, не завершённый объект. *)
Theorem process_hierarchy_is_generative_ascent :
  (forall n (f : Level n -> Level (S n)), exists g, forall x, g <> f x)   (* строгий подъём *)
  /\ (forall n, exists m, (n < m)%nat)                                    (* нет вершины *)
  /\ omega = OLim level_index                                            (* индекс = ω-процесс *)
  /\ (forall B, exists n, (tower_height_flow n > B)%nat).                 (* незамкнуто => role-limit *)
Proof.
  split; [ apply cantor_level | ].
  split; [ intro n; exists (S n); lia | ].
  split; [ exact tower_height_is_limit_process | ].
  apply tower_height_unbounded.
Qed.
