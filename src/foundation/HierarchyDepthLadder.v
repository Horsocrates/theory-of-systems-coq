(** * HierarchyDepthLadder.v — НАПРАВЛЕНИЕ «Процессная иерархия», ступень 2 (глубина = рунг).

   Ступень 1 (ProcessHierarchyCore) дала восходящую башню роль-типов Level n.  Здесь — её
   ГЛУБИНА: этаж башни соответствует рунгу ВСЕВЕДЕНИЯ (RoleLimitLadder), то есть тому, сколько
   завершённой бесконечности требует вопрос на этом этаже.  Подъём role-limit-стороны градуирован, и
   градация КОНСТРУКТИВНА (видна лишь через P4: классически схлопывается).

   ★ Соответствие этаж -> рунг (genuine):
     -- этаж 0 (Level 0 = nat): равенство РАЗРЕШИМО — рунг 0, Element, без всякого всеведения;
     -- этаж 1 (Level 1 = nat->bool, роль-тип): вопрос «срабатывает или никогда» есть РОВНО LPO
        (level1_decision_is_LPO) — рунг LPO (Σ⁰₁);
     -- выше: каскад над этажом 1 — рунг LPO_omega, и LPO_omega -> LPO (RoleLimitLadder.lpo_omega_lpo):
        более высокий этаж требует строго больше всеведения.

   ★ Градация КОНСТРУКТИВНА (честный P4-пункт): LEM -> decide_level1 (lem_decides_level1) — классически
     этаж 1 решается, рунг СХЛОПЫВАЕТСЯ; глубина видна только без LEM.  Это и значит «подъём role-limit-
     стороны виден лишь через P4».

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом (LEM/LPO — Prop-ГИПОТЕЗЫ, не аксиомы).  Это НИЖНИЕ рунги
   соответствия этаж<->всеведение (0=разрешимо, 1=LPO) + направление градации; ПОЛНОГО изоморфизма
   этаж_n <-> рунг_n для всех n НЕ строим (выше LPO_omega — конструктивная reverse math, цитата
   RoleLimitLadder).  Строгость рунгов (необратимость импликаций) — модель, не здесь (как в RoleLimitLadder).

   Elements: булева g : Level 1; равенство на Level 0.
   Roles:    этаж = вопрос данной кванторной глубины; рунг = требуемое всеведение; LEM = оракул-схлоп.
   Rules:    этаж 0 разрешим; этаж 1 = LPO; LEM схлопывает; LPO_omega -> LPO (выше строго сильнее).
   ДИАГНОСТИКА (P4): глубина этажа = рунг всеведения; градация конструктивна (классически плоско).

   STATUS: 4 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.
From ToS Require Import foundation.ProcessHierarchyCore.
From ToS Require Import foundation.RoleLimitLadder.

(** Этаж 0 (Level 0 = nat): равенство РАЗРЕШИМО — рунг 0, Element. *)
Lemma level0_decidable : forall x y : Level 0, {x = y} + {x <> y}.
Proof. apply Nat.eq_dec. Qed.

(** Решение на этаже 1 (роль-тип nat -> bool): «срабатывает или никогда». *)
Definition decide_level1 : Prop :=
  forall g : Level 1, (exists n, g n = true) \/ (forall n, g n = false).

(** Это РОВНО LPO: этаж 1 башни = рунг LPO (Σ⁰₁-всеведение). *)
Lemma level1_decision_is_LPO : decide_level1 <-> LPO.
Proof. unfold decide_level1, LPO. split; intro H; exact H. Qed.

(** Градация КОНСТРУКТИВНА: классически этаж 1 решается (рунг схлопывается); под P4 — нет. *)
Lemma lem_decides_level1 : LEM -> decide_level1.
Proof.
  intros lem g. destruct (lem (exists n, g n = true)) as [H | H].
  - left. exact H.
  - right. intro n. destruct (g n) eqn:E.
    + exfalso. apply H. exists n. exact E.
    + reflexivity.
Qed.

(** Капстоун: глубина этажа = рунг всеведения; восходящая градация, видимая лишь через P4. *)
Theorem hierarchy_depth_is_omniscience_grading :
  (forall x y : Level 0, x = y \/ x <> y)   (* этаж 0: разрешимо (Element, рунг 0) *)
  /\ (decide_level1 <-> LPO)                 (* этаж 1: рунг LPO *)
  /\ (LEM -> decide_level1)                  (* классически рунг схлопывается *)
  /\ (LPO_omega -> LPO).                      (* выше: каскадный рунг строго сильнее *)
Proof.
  split; [ intros x y; destruct (level0_decidable x y); [left | right]; assumption | ].
  split; [ apply level1_decision_is_LPO | ].
  split; [ apply lem_decides_level1 | ].
  apply lpo_omega_lpo.
Qed.
