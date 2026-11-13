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

   STATUS: 9 Qed, 0 Admitted, 0 axioms
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

(* ================================================================= *)
(* Nov 2026: THE VALUE OF BACKWARD INDUCTION IS THE WINNER             *)
(* ================================================================= *)

(* finite_game_determined above says only that a boolean is true or false.
   Here mover_wins is tied to winning: every position of a finite tree is won
   by exactly one side, and mover_wins computes which. *)

(* Win g : the player to move at g can force a win;
   Lose g: whatever the player to move does, the opponent can force a win.
   A node with no moves is lost for the player to move (as in mover_wins). *)
Inductive Win : GameTree -> Prop :=
  | win_leaf : Win (GLeaf true)
  | win_node : forall cs c, In c cs -> Lose c -> Win (GNode cs)
with Lose : GameTree -> Prop :=
  | lose_leaf : Lose (GLeaf false)
  | lose_node : forall cs, (forall c, In c cs -> Win c) -> Lose (GNode cs).

Fixpoint any_neg (l : list GameTree) : bool :=
  match l with
  | nil => false
  | c :: rest => orb (negb (mover_wins c)) (any_neg rest)
  end.

Lemma mover_wins_node : forall cs, mover_wins (GNode cs) = any_neg cs.
Proof.
  induction cs as [| c cs IH].
  - reflexivity.
  - change (mover_wins (GNode (c :: cs)))
      with (orb (negb (mover_wins c)) (mover_wins (GNode cs))).
    rewrite IH. reflexivity.
Qed.

Lemma GameTree_ind' (P : GameTree -> Prop) :
  (forall b, P (GLeaf b)) ->
  (forall cs, (forall c, In c cs -> P c) -> P (GNode cs)) ->
  forall g, P g.
Proof.
  intros Hleaf Hnode. fix IH 1. intros [b | cs].
  - apply Hleaf.
  - apply Hnode. induction cs as [| c cs IHcs].
    + intros c [].
    + intros c' [Heq | Hin].
      * rewrite <- Heq. apply IH.
      * apply IHcs. exact Hin.
Qed.

Lemma any_neg_true : forall cs, any_neg cs = true ->
  exists c, In c cs /\ mover_wins c = false.
Proof.
  induction cs as [| c cs IH]; simpl; intro H; [discriminate |].
  apply orb_true_iff in H. destruct H as [H | H].
  - exists c. split; [left; reflexivity | apply negb_true_iff; exact H].
  - destruct (IH H) as [c' [Hin Hc']]. exists c'. split; [right; exact Hin | exact Hc'].
Qed.

Lemma any_neg_false : forall cs, any_neg cs = false ->
  forall c, In c cs -> mover_wins c = true.
Proof.
  induction cs as [| c0 cs IH]; simpl; intros H c Hin; [destruct Hin |].
  apply orb_false_iff in H. destruct H as [H1 H2].
  destruct Hin as [Heq | Hin].
  - rewrite <- Heq. apply negb_false_iff. exact H1.
  - apply IH; assumption.
Qed.

(* backward induction computes the winner *)
Theorem backward_induction_sound : forall g,
  (mover_wins g = true -> Win g) /\ (mover_wins g = false -> Lose g).
Proof.
  induction g as [b | cs IH] using GameTree_ind'.
  - split; intro H; simpl in H; rewrite H; constructor.
  - rewrite mover_wins_node. split; intro H.
    + destruct (any_neg_true cs H) as [c [Hin Hc]].
      apply (win_node cs c Hin). exact (proj2 (IH c Hin) Hc).
    + apply lose_node. intros c Hin.
      exact (proj1 (IH c Hin) (any_neg_false cs H c Hin)).
Qed.

(* a position cannot be won by both sides *)
Theorem win_lose_exclusive : forall g, Win g -> Lose g -> False.
Proof.
  induction g as [b | cs IH] using GameTree_ind'; intros Hw Hl.
  - inversion Hw; subst. inversion Hl.
  - inversion Hw as [| cs' c Hin Hlc Heq]; subst.
    inversion Hl as [| cs' Hall Heq]; subst.
    exact (IH c Hin (Hall c Hin) Hlc).
Qed.

(* determinacy of finite games: every position is won by exactly one side,
   and the backward-induction value says which *)
Theorem finite_game_strategically_determined : forall g,
  (Win g \/ Lose g) /\ ~ (Win g /\ Lose g) /\
  (mover_wins g = true <-> Win g) /\ (mover_wins g = false <-> Lose g).
Proof.
  intro g. destruct (backward_induction_sound g) as [Hw Hl].
  split; [| split; [| split]].
  - destruct (mover_wins g); [left; apply Hw | right; apply Hl]; reflexivity.
  - intros [H1 H2]. exact (win_lose_exclusive g H1 H2).
  - split; [exact Hw |]. intro H.
    destruct (mover_wins g) eqn:E; [reflexivity |].
    exfalso. exact (win_lose_exclusive g H (Hl eq_refl)).
  - split; [exact Hl |]. intro H.
    destruct (mover_wins g) eqn:E; [| reflexivity].
    exfalso. exact (win_lose_exclusive g (Hw eq_refl) H).
Qed.
