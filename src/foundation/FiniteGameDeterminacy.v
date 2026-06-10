(** * FiniteGameDeterminacy.v — детерминированность откатывается к обратной индукции на конечном дереве.

   «Стена» борелевской (Мартина) детерминированности (Часть X): классически доказательство лезет по
   ЗАВЕРШЁННОЙ башне итерированных степеней (борелевская иерархия до ранга ~omega_1).  ОТКАТ (метод P4):
   на КОНЕЧНОМ дереве игры победитель «того, чей ход» вычисляется ОБРАТНОЙ ИНДУКЦИЕЙ — тотальная
   вычислимая функция, без всякой башни.  Завершённая башня = ZFC-упаковка; борелевское расширение —
   процессно-индексированная иерархия роль-типов (НЕ ПРИВЛЕЧЕНО как процесс, не стена).

   Elements: конечные деревья игры, позиции, партии.
   Roles:    стратегия = процесс (правило позиция -> ход); детерминированность = роль «у кого выигрыш».
   Rules:    обратная индукция mover_wins (узел выигрышен <=> есть ход, после которого противник проигр.);
             тотальность mover_wins => детерминированность.
   ДИАГНОСТИКА (P4): завершённая бесконечность здесь = упаковка башни; конечная игра свободна.

   STATUS: 2 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Bool.
Import ListNotations.

Inductive GameTree :=
  | GLeaf (mover_wins_here : bool)
  | GNode (children : list GameTree).

(** Победитель «того, чей ход» — обратная индукция: ход выигрышен, если есть ребёнок, после которого
    ПРОТИВНИК (теперь ходящий) проигрывает.  Тотальная вычислимая функция на конечном дереве. *)
Fixpoint mover_wins (g : GameTree) : bool :=
  match g with
  | GLeaf b => b
  | GNode cs =>
      (fix any (l : list GameTree) : bool :=
         match l with
         | nil => false
         | c :: rest => orb (negb (mover_wins c)) (any rest)
         end) cs
  end.

(** Детерминированность: победитель определён (тотальный bool) — без завершённой башни. *)
Theorem finite_game_determined : forall g, mover_wins g = true \/ mover_wins g = false.
Proof. intro g. destruct (mover_wins g); [left | right]; reflexivity. Qed.

Example game_mover_wins :
  mover_wins (GNode (GLeaf false :: GLeaf true :: nil)) = true.
Proof. reflexivity. Qed.
