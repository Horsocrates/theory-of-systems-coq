(** * SeedMeasureBridge.v — B1 направления: мост СЕМЕНИ undecided ↔ МЕРА.
      Ультрафильтр ЕСТЬ 2-значная конечно-аддитивная мера; undecided S = ровно то, что 2-значная
      Фреше-ПРЕМЕРА оставляет НЕОПРЕДЕЛЁННЫМ (ни 0, ни 1).  Фильтр = мера = алгебра — один объект.

   ★ ЧЕСТНАЯ ПОПРАВКА (правило R1 плана: мост или СТОП).  Наивный мост «undecided ↔ НЕИЗМЕРИМОЕ» — ЛОЖЕН:
   Evens Фреше-undecided, но DENSITY-ИЗМЕРИМО (плотность 1/2).  «Доказать» его = переописание.  Genuine
   мост ДРУГОЙ и стандартный: ультрафильтр = 2-значная конечно-аддитивная мера (Stone), а undecided S =
   то, что КАНОНИЧЕСКАЯ 2-значная Фреше-премера (cofinite↦1, finite↦0) НЕ определяет.  Density-1/2 — это
   ВЕЩЕСТВЕННАЯ мера (другая, Element-ish); РОВНО 2-значная (= ультрафильтр) — role-limit.

   ★ МОСТ (genuine, доказано конструктивно):
     (undecided → premeasure undetermined)  undecided S ⟹ ~cofinite S ∧ ~finite S — 2-значная Фреше-премера
       НЕ присваивает S ни 1 (cofinite), ни 0 (finite);
     (uf-мера resolves)                       любая 2-значная Фреше-расширяющая комплемент-уважающая мера
       (= ультрафильтр) ПРАЙМ: m S = 1 ∨ m ¬S = 1 — тотализует то, что премера оставила открытым.
   Один объект — три вида: фильтр (undecided), мера (uf-мера = ультрафильтр), алгебра (делитель нуля, A1).

   ★ КОНСТРУКТИВНО (0 аксиом).  undecided определён ПОЗИТИВНО (cofinal S ∧ cofinal ¬S), поэтому
   undecided ⟹ ~cofinite ∧ ~finite БЕЗ classic (прямое противоречие cofinal с eventually).

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  Доказано: undecided ⟹ премера-undetermined (→ только;
   ОБРАТНОЕ undetermined ⟹ undecided нужен classic/DNE — честно НЕ доказывается); uf-мера прайм/resolves.
   ⚠ Это МОСТ-РЕИНСТАНЦИЯ стандартного факта (ультрафильтр = 2-значная FA-мера, Stone), связанного с undecided
   и (цитата A1) с делителем нуля.  СУЩЕСТВОВАНИЕ нетривиальной uf-меры = AC-фрагмент, НЕ ассертим.  Наивный
   мост «undecided↔неизмеримое» ЧЕСТНО отвергнут (Evens — контрпример).

   Elements: множества nat→bool; cofinite/finite/cofinal/undecided; is_uf_measure; evens.
   Roles:    undecided=неопределённость-премеры; uf-мера=тотализация (ультрафильтр); cofinite/finite=определённые.
   Rules:    undecided S ⟹ ~cofinite S ∧ ~finite S; uf-мера прайм; forced на cofinite/finite, free на undecided.

   ============ E/R/R разбор (осн. + образующие + вложенные + элемент-как-система) ============
     ОСН.: undecided (фильтр) → недоопределённость 2-знач. Фреше-премеры (мера) → разрешается uf-мерой.
     Rules (L5): undecided S ⟹ ~cofinite ∧ ~finite (премера undetermined); uf-мера прайм; resolves undecided.
     Roles (L4): undecided=неопределённость-премеры; uf-мера=тотализация (ультрафильтр); cofinite/finite=определённые.
     Elements  : nat→bool; cofinite/finite/cofinal/undecided; is_uf_measure; evens.
     ОБРАЗУЮЩИЕ: синтез XVIII (undecided); A1 UnitZeroDivisorBoundary (m(Evens)=unit-сторона, цитата);
                 IllusoryConstructions (μ=2μ мера-обструкция, цитата); Stone (ультрафильтр=2-знач.мера, цитата).
     ВЛОЖЕННЫЕ : undecided ↔ premeasure-undetermined (доказано →) ↔ uf-measure-resolved.
     ★ ЭЛЕМЕНТ-КАК-СИСТЕМА (2-значная мера): Elements — значения на множествах; Roles — тотализация размера;
                 Rules — forced на cofinite/finite, FREE на undecided (= ультрафильтрный выбор).
   ДИАГНОСТИКА (P4): конструктивно (позитивный undecided ⟹ ~cofinite/~finite прямо) => 0 акс. ЧЕСТНО: обратное
                 нужен classic; density-1/2 = вещ. мера (Element); 2-знач. uf-мера = role-limit (AC, не ассертим);
                 наивный мост отвергнут (Evens контрпример).

   STATUS: 10 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  Множества как nat→bool; Фреше-премера (cofinite/finite); undecided      *)
(* ===================================================================== *)

(** S коконечно: истинно на всём хвосте (Фреше-премера присваивает 1). *)
Definition cofinite (S : nat -> bool) : Prop := exists N, forall n, (N <= n)%nat -> S n = true.

(** S конечно: ложно на всём хвосте (Фреше-премера присваивает 0). *)
Definition finite (S : nat -> bool) : Prop := cofinite (fun n => negb (S n)).

(** S истинно бесконечно часто (позитивно — конструктивно). *)
Definition cofinal (S : nat -> bool) : Prop := forall N, exists n, (N <= n)%nat /\ S n = true.

(** ★ Неразрешённое различение: и S, и ¬S истинны бесконечно часто (Фреше не решает). *)
Definition undecided (S : nat -> bool) : Prop := cofinal S /\ cofinal (fun n => negb (S n)).

Definition evens (n : nat) : bool := Nat.even n.

(** ★ Ультрафильтр КАК 2-значная мера (Stone): содержит ℕ, уважает комплемент (прайм), монотонна. *)
Definition is_uf_measure (m : (nat -> bool) -> bool) : Prop :=
  m (fun _ => true) = true
  /\ (forall S, m (fun n => negb (S n)) = negb (m S))
  /\ (forall S T, (forall n, S n = true -> T n = true) -> m S = true -> m T = true).

(* ===================================================================== *)
(*  Evens — каноническое неразрешённое различение                          *)
(* ===================================================================== *)

Lemma cofinal_evens : cofinal evens.
Proof.
  intro N. exists (2 * N)%nat. split; [ lia |].
  unfold evens. replace (2 * N)%nat with (0 + 2 * N)%nat by lia.
  rewrite Nat.even_add_mul_2. reflexivity.
Qed.

Lemma cofinal_odds : cofinal (fun n => negb (evens n)).
Proof.
  intro N. exists (2 * N + 1)%nat. split; [ lia |].
  unfold evens. replace (2 * N + 1)%nat with (1 + 2 * N)%nat by lia.
  rewrite Nat.even_add_mul_2. reflexivity.
Qed.

Lemma undecided_evens : undecided evens.
Proof. split; [ exact cofinal_evens | exact cofinal_odds ]. Qed.

(* ===================================================================== *)
(*  ★ Мост: undecided ⟹ Фреше-премера НЕ определяет S                      *)
(* ===================================================================== *)

(** undecided S ⟹ S НЕ коконечно (премера не присваивает 1): ¬S бесконечно часто. *)
Lemma undecided_not_cofinite : forall S, undecided S -> ~ cofinite S.
Proof.
  intros S [HcS HcN] [N HN]. destruct (HcN N) as [n [Hn Hneg]].
  specialize (HN n Hn). rewrite HN in Hneg. simpl in Hneg. discriminate.
Qed.

(** undecided S ⟹ S НЕ конечно (премера не присваивает 0): S бесконечно часто. *)
Lemma undecided_not_finite : forall S, undecided S -> ~ finite S.
Proof.
  intros S [HcS HcN] [N HN]. destruct (HcS N) as [n [Hn Hpos]].
  specialize (HN n Hn). rewrite Hpos in HN. simpl in HN. discriminate.
Qed.

(** ★ undecided S ⟹ 2-значная Фреше-премера оставляет S НЕОПРЕДЕЛЁННЫМ (ни 1, ни 0). *)
Lemma undecided_premeasure_undetermined : forall S, undecided S -> ~ cofinite S /\ ~ finite S.
Proof.
  intros S Hu. split;
    [ apply undecided_not_cofinite | apply undecided_not_finite ]; exact Hu.
Qed.

(** Анкер: Фреше-премера не определяет Evens. *)
Lemma evens_premeasure_undetermined : ~ cofinite evens /\ ~ finite evens.
Proof. apply undecided_premeasure_undetermined. exact undecided_evens. Qed.

(* ===================================================================== *)
(*  ★ uf-мера (= ультрафильтр) ТОТАЛИЗУЕТ то, что премера оставила открытым *)
(* ===================================================================== *)

(** ★ 2-значная uf-мера ПРАЙМ: для всякого S ровно одно из S, ¬S имеет меру 1. *)
Lemma uf_measure_prime :
  forall m S, is_uf_measure m -> m S = true \/ m (fun n => negb (S n)) = true.
Proof.
  intros m S [_ [Hcompl _]]. destruct (m S) eqn:E.
  - left. reflexivity.
  - right. rewrite Hcompl, E. reflexivity.
Qed.

(** ★ uf-мера РАЗРЕШАЕТ undecided S (которое Фреше-премера оставила открытым) — выбор role-limit. *)
Theorem uf_measure_resolves_undecided :
  forall m S, is_uf_measure m -> undecided S -> m S = true \/ m (fun n => negb (S n)) = true.
Proof. intros m S Hm _. apply uf_measure_prime. exact Hm. Qed.

(* ===================================================================== *)
(*  Капстоун: один объект — фильтр, мера, алгебра                           *)
(* ===================================================================== *)

(** ★ Мост семени undecided ↔ мера (0 аксиом):
      (undecided→премера)  undecided S ⟹ 2-значная Фреше-премера НЕ определяет S (ни 1, ни 0);
      (Evens)              Evens — undetermined премерой (анкер);
      (uf-мера resolves)   2-значная uf-мера (= ультрафильтр) ПРАЙМ — тотализует открытое;
      (Evens undecided)    Evens — семя undecided.
    Один объект, три вида: фильтр (undecided), мера (uf-мера = ультрафильтр = 2-знач. FA-мера, Stone),
    алгебра (делитель нуля even_ind, A1).  ЧЕСТНО: наивный «undecided↔неизмеримое» отвергнут (Evens
    density-измеримо 1/2); РОВНО 2-значная мера = role-limit; существование uf-меры = AC, НЕ ассертим. *)
Theorem seed_measure_bridge :
  (forall S, undecided S -> ~ cofinite S /\ ~ finite S)
  /\ (~ cofinite evens /\ ~ finite evens)
  /\ (forall m S, is_uf_measure m -> m S = true \/ m (fun n => negb (S n)) = true)
  /\ undecided evens.
Proof.
  split; [ exact undecided_premeasure_undetermined |].
  split; [ exact evens_premeasure_undetermined |].
  split; [ exact uf_measure_prime | exact undecided_evens ].
Qed.
