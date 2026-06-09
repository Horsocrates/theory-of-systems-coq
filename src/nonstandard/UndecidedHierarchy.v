(** * UndecidedHierarchy.v — C направления: дальняя сторона границы ГРАДУИРОВАНА (не бинарна).
      Две оси role-limit: разрешимость ЧЛЕНСТВА (Тьюринг) vs разрешимость ВЕЛИЧИНЫ (LPO).
      ★ Ключ: role-limit-ность НЕ в множестве (evens разрешимо поэлементно), а в ТОТАЛИЗАЦИИ (величина).

   КОНТЕКСТ.  A1–E установили: граница = обратимость, дальняя сторона = одно семя negb.  ЗДЕСЬ — уточнение:
   дальняя сторона НЕ однородна, а СТРАТИФИЦИРОВАНА по тому, ГДЕ живёт неразрешимость:
     -- axis 1 (ЧЛЕНСТВО, Тьюринг): разрешимо ли n ∈ S?  Для всякого nat→bool — ДА; для halting — НЕТ;
     -- axis 2 (ВЕЛИЧИНА, LPO): решает ли Фреше «велико ли S»?  Для конечного — ДА; для undecided — НЕТ.
   Три страты: Element (разрешимы обе оси) ⊏ LPO-role-limit (членство разрешимо, величина — нет: evens)
   ⊏ Тьюринг-role-limit (членство неразрешимо: halting).

   ★ ГЕНУИННЫЙ АНКЕР (машинно): evens имеет РАЗРЕШИМОЕ членство (Nat.even вычислима), НО undecided величину
   (Фреше не решает).  И singleton имеет разрешимое членство И конечную (decided) величину — Element.
   Значит ОБА разрешимы поэлементно; различает их ВЕЛИЧИНА (axis 2 = LPO-граница), НЕ членство.  Вывод:
   role-limit-ность evens — НЕ в «невычислимости множества», а в неразрешимости ТОТАЛИЗАЦИИ (велико/мало).

   ★ КОНСТРУКТИВНО (0 аксиом).  decidable_pred для nat→bool — destruct (S n); singleton finite — явно.

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  Доказано: всякое nat→bool множество разрешимо поэлементно;
   evens — разрешимое членство + undecided величина (LPO-рунг); singleton — Element (конечная величина).
   ⚠ Тьюринг-рунг (halting: НЕразрешимое членство) — ЦИТАТА (`cs/HaltingRoleLimit`; non-computable nat→Prop
   нельзя ПРЕДЪЯВИТЬ конструктивно в Coq).  Genuine = LPO-рунг анкор (role-limit при разрешимом членстве) +
   наблюдение градации (два фронтира: LPO величины ⊏ Тьюринг членства).  H69 (LPO-лестница) — соседний.

   Elements: nat→bool; decidable_pred; cofinite/finite/cofinal/undecided; evens/singleton.
   Roles:    членство=axis-1 (Тьюринг); величина=axis-2 (LPO); рунг=глубина role-limit.
   Rules:    nat→bool ⟹ разрешимое членство; evens=разрешимо+undecided (LPO); singleton=разрешимо+конечно (Element).

   ============ E/R/R разбор (осн. + образующие + вложенные + элемент-как-система) ============
     ОСН.: дальняя сторона границы градуирована по оси неразрешимости (членство/Тьюринг vs величина/LPO).
     Rules (L5): nat→bool ⟹ разрешимое членство; evens=разрешимо+undecided величина (LPO); singleton=Element;
                 halting=неразрешимое членство (Тьюринг, цитата).
     Roles (L4): членство=axis-1 (Тьюринг); величина=axis-2 (LPO); рунг=глубина.
     Elements  : nat→bool; decidable_pred; cofinite/finite/undecided; evens/singleton.
     ОБРАЗУЮЩИЕ: B1/синтез XVIII (undecided=величина); H69 RoleLimitLadder (LPO); cs/HaltingRoleLimit (Тьюринг, цитата).
     ВЛОЖЕННЫЕ : Element (singleton) ⊏ LPO-role-limit (evens) ⊏ Тьюринг-role-limit (halting).
     ★ ЭЛЕМЕНТ-КАК-СИСТЕМА (evens): разрешима поэлементно (Element-членство), но роль «велико?» неразрешима (LPO)
                 ⟹ role-limit не в множестве, а в тотализации.
   ДИАГНОСТИКА (P4): конструктивно (decidable_pred явно; singleton finite явно) => 0 акс. ЧЕСТНО: Тьюринг-рунг =
                 цитата (non-computable нельзя предъявить в Coq); genuine = LPO-анкор + градация.

   STATUS: 6 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  Множества nat→bool; две оси разрешимости                               *)
(* ===================================================================== *)

Definition cofinite (S : nat -> bool) : Prop := exists N, forall n, (N <= n)%nat -> S n = true.
Definition finite   (S : nat -> bool) : Prop := cofinite (fun n => negb (S n)).
Definition cofinal  (S : nat -> bool) : Prop := forall N, exists n, (N <= n)%nat /\ S n = true.
Definition undecided (S : nat -> bool) : Prop := cofinal S /\ cofinal (fun n => negb (S n)).

(** axis 1 (ЧЛЕНСТВО, Тьюринг): разрешим ли предикат поэлементно (sumbool — в Type). *)
Definition decidable_pred (P : nat -> Prop) : Type := forall n, {P n} + {~ P n}.

Definition evens (n : nat) : bool := Nat.even n.
Definition singleton (n : nat) : bool := Nat.eqb n 0.

(* ===================================================================== *)
(*  axis 1: ВСЯКОЕ nat→bool множество имеет РАЗРЕШИМОЕ членство             *)
(* ===================================================================== *)

(** ★ Любое nat→bool множество разрешимо поэлементно — Element-членство (Тьюринг-ось ниже границы). *)
Lemma bool_pred_decidable : forall (S : nat -> bool), decidable_pred (fun n => S n = true).
Proof.
  intros S n. destruct (S n) eqn:E.
  - left. reflexivity.
  - right. discriminate.
Qed.

(* ===================================================================== *)
(*  axis 2 (ВЕЛИЧИНА, LPO): evens — undecided; singleton — конечно         *)
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

(** ★ evens — undecided ВЕЛИЧИНА (Фреше не решает «велико ли») — LPO-рунг. *)
Lemma undecided_evens : undecided evens.
Proof. split; [ exact cofinal_evens | exact cofinal_odds ]. Qed.

(** ★ singleton {0} — КОНЕЧНО (величина РЕШЕНА: мало) — Element. *)
Lemma singleton_finite : finite singleton.
Proof.
  exists 1%nat. intros [|m] Hn; [ lia | reflexivity ].
Qed.

(* ===================================================================== *)
(*  Капстоун: дальняя сторона границы — два фронтира (LPO ⊏ Тьюринг)         *)
(* ===================================================================== *)

(** ★ Градация дальней стороны границы (0 аксиом):
      (axis 1)        всякое nat→bool множество разрешимо поэлементно (Element-членство);
      (LPO-рунг)      evens — разрешимое членство, НО undecided ВЕЛИЧИНА (Фреше не решает);
      (Element)       singleton {0} — разрешимое членство И конечная (decided) величина.
    evens и singleton ОБА разрешимы поэлементно; различает их ВЕЛИЧИНА (axis 2 = LPO-граница), НЕ членство.
    ⟹ role-limit-ность evens — в ТОТАЛИЗАЦИИ (велико/мало), НЕ в множестве.  Глубже — Тьюринг-рунг
    (halting: неразрешимое членство, axis 1), цитата `cs/HaltingRoleLimit`.  Дальняя сторона = два фронтира:
    LPO (величина) ⊏ Тьюринг (членство).  (Разрешимость членства обеих — `bool_pred_decidable`, axis 1.) *)
Theorem undecided_hierarchy :
  undecided evens /\ finite singleton.
Proof.
  split; [ exact undecided_evens | exact singleton_finite ].
Qed.
