(** * PowersetRoleType.v — «степенной объект» откатывается к роль-типу N -> bool.

   «Стена» завершённого P(N) (Часть X): классически P(N) — завершённое МНОЖЕСТВО всех подмножеств,
   несчётный объект.  ОТКАТ (метод P4): в «P(N)» слиты (a) ОПЕРАЦИЯ/роль «подмножество» = предикат
   N -> bool (процесс решений о принадлежности) и (b) завершённый СБОР всех предикатов в готовую
   тотальность.  Бесконечность сидит ТОЛЬКО в (b), и (b) нигде не нужен: всё содержание — про роль-тип.

   ★ Element-сторона свободна: конечный powerset = ровно 2^n подмножеств (powerset_card), вычислимо.
   ★ Ядро «несчётности» БЕЗ завершённого объекта: роль-тип N -> bool не перечислим — диагональ
     (cantor_bool_seq).  Это и есть то, что ZFC паковал в завершённый P(N).
   Завершённый P(N) как Element — артефакт ZFC-упаковки, а не граница нашей системы.

   Elements: конечные подмножества (powerset l, 2^n штук); булевы последовательности N -> bool.
   Roles:    подмножество = роль-предикат-процесс; «степень» = роль-тип N -> bool (пространство процессов).
   Rules:    P1 (роль-тип на уровень выше N, не Element того же уровня); диагональ (нет сюръекции
             N -> (N -> bool)).
   ДИАГНОСТИКА (P4): завершённая бесконечность здесь = упаковка (b); операция и ядро-несчётность свободны.

   STATUS: 3 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.

(** Конечный степенной объект как СПИСОК — никакой завершённой бесконечности. *)
Fixpoint powerset {A : Type} (l : list A) : list (list A) :=
  match l with
  | nil => nil :: nil
  | x :: xs => let ps := powerset xs in ps ++ map (fun s => x :: s) ps
  end.

(** Element-сторона: ровно 2^n подмножеств. *)
Lemma powerset_card : forall {A : Type} (l : list A), length (powerset l) = 2 ^ length l.
Proof.
  intros A l. induction l as [|x xs IH].
  - reflexivity.
  - simpl. rewrite length_app, length_map, IH. lia.
Qed.

Example powerset_3_has_8 : length (powerset (1 :: 2 :: 3 :: nil)) = 8.
Proof. reflexivity. Qed.

(** Ядро «P(N) несчётно» БЕЗ завершённого объекта: роль-тип N -> bool не перечислим (диагональ). *)
Theorem cantor_bool_seq :
  forall f : nat -> (nat -> bool), exists g : nat -> bool, forall n, g <> f n.
Proof.
  intros f. exists (fun n => negb (f n n)). intros n Heq.
  apply (f_equal (fun h => h n)) in Heq. simpl in Heq.
  destruct (f n n); discriminate.
Qed.
