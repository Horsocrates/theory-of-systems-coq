(** * ZermeloDeterminacy.v — every game of finite length is determined

    Elements: a history of moves (GameState), the two strategies, a winning
              condition W, the number of rounds K (all from BorelDeterminacy.v;
              moves are natural numbers, W is an arbitrary predicate).
    Roles:    WinI W r h — "player I FORCES W from history h with r rounds
              left"; a strategy plays "keeps the invariant".
    Rules:    by excluded middle player I either forces W from the empty
              history or does not; the strategy of the side that holds the
              invariant takes, at every history, a move that keeps it.
    P4 diagnostic: the game has finitely many rounds, but infinitely many
              moves at each round and an undecidable W — so "there is a good
              move at every history" has to be turned into a strategy
              FUNCTION.  The witness is not unique: this is L4_witness in its
              full strength, on top of excluded middle.

    zermelo_determinacy : forall W K, determined W K
        — Print Assumptions: Classical_Prop.classic + ToS_Axioms.L4_witness.
    BorelDeterminacy.weak_determinacy is only "P or not P" for "player I has a
    winning strategy"; here one of the TWO players gets a strategy.  For
    finite game TREES the same is proved with no assumptions at all:
    foundation/FiniteGameDeterminacy.finite_game_strategically_determined.

    STATUS: 6 Qed, 0 Admitted, no axioms of its own
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import List Lia Bool PeanoNat.
Import ListNotations.
From ToS Require Import ToS_Axioms.
From ToS Require Import settheory.BorelDeterminacy.

(* player I can force W from history h with r rounds left *)
Fixpoint WinI (W : GameState -> Prop) (r : nat) (h : GameState) : Prop :=
  match r with
  | O => W h
  | S r' => if Nat.even (length h)
            then exists m, WinI W r' (h ++ [m])
            else forall m, WinI W r' (h ++ [m])
  end.

Lemma choose_ex : forall (Q : nat -> Prop), exists m, (exists m', Q m') -> Q m.
Proof.
  intro Q. destruct (classic (exists m', Q m')) as [[m Hm] | Hn].
  - exists m. intros _. exact Hm.
  - exists 0. intro H. contradiction.
Qed.

Definition pick (Q : nat -> Prop) : nat :=
  proj1_sig (@ToS_Axioms.L4_witness nat _ (choose_ex Q)).

Lemma pick_spec : forall Q : nat -> Prop, (exists m, Q m) -> Q (pick Q).
Proof.
  intros Q H. unfold pick.
  exact (proj2_sig (@ToS_Axioms.L4_witness nat _ (choose_ex Q)) H).
Qed.

Definition sI_win (W : GameState -> Prop) (K : nat) : Strategy_I :=
  fun h => pick (fun m => WinI W (K - S (length h)) (h ++ [m])).

Definition sII_spoil (W : GameState -> Prop) (K : nat) : Strategy_II :=
  fun h => pick (fun m => ~ WinI W (K - S (length h)) (h ++ [m])).

Lemma play_step : forall sI sII k,
  play sI sII (S k) =
  play sI sII k ++
    [if Nat.even (length (play sI sII k))
     then sI (play sI sII k) else sII (play sI sII k)].
Proof. reflexivity. Qed.

Lemma winI_invariant : forall W K sII,
  WinI W K [] ->
  forall k, (k <= K)%nat -> WinI W (K - k) (play (sI_win W K) sII k).
Proof.
  intros W K sII H0. induction k as [| k IH]; intro Hk.
  - rewrite Nat.sub_0_r. exact H0.
  - assert (Hk' : (k <= K)%nat) by lia. specialize (IH Hk').
    pose proof (play_length (sI_win W K) sII k) as Hlen.
    replace (K - k)%nat with (S (K - S k)) in IH by lia.
    cbn [WinI] in IH.
    rewrite play_step.
    set (h := play (sI_win W K) sII k) in *.
    revert IH. destruct (Nat.even (length h)) eqn:Ev; intro IH.
    + unfold sI_win. rewrite Hlen.
      apply (pick_spec (fun m => WinI W (K - S k) (h ++ [m]))). exact IH.
    + apply IH.
Qed.

Lemma notwinI_invariant : forall W K sI,
  ~ WinI W K [] ->
  forall k, (k <= K)%nat -> ~ WinI W (K - k) (play sI (sII_spoil W K) k).
Proof.
  intros W K sI H0. induction k as [| k IH]; intro Hk.
  - rewrite Nat.sub_0_r. exact H0.
  - assert (Hk' : (k <= K)%nat) by lia. specialize (IH Hk').
    pose proof (play_length sI (sII_spoil W K) k) as Hlen.
    replace (K - k)%nat with (S (K - S k)) in IH by lia.
    cbn [WinI] in IH.
    rewrite play_step.
    set (h := play sI (sII_spoil W K) k) in *.
    revert IH. destruct (Nat.even (length h)) eqn:Ev; intro IH.
    + intro Hw. apply IH. exists (sI h). exact Hw.
    + unfold sII_spoil. rewrite Hlen.
      apply (pick_spec (fun m => ~ WinI W (K - S k) (h ++ [m]))).
      destruct (classic
                  (exists m, ~ WinI W (K - S k) (h ++ [m]))) as [Hex | Hno];
        [exact Hex |].
      exfalso. apply IH. intro m.
      destruct (classic (WinI W (K - S k) (h ++ [m])))
        as [Hy | Hn]; [exact Hy |].
      exfalso. apply Hno. exists m. exact Hn.
Qed.

(* Zermelo: every game of finite length K is determined *)
Theorem zermelo_determinacy : forall W K, determined W K.
Proof.
  intros W K. destruct (classic (WinI W K [])) as [Hw | Hn].
  - left. exists (sI_win W K). intro sII. unfold wins_I.
    pose proof (winI_invariant W K sII Hw K (Nat.le_refl _)) as H.
    rewrite Nat.sub_diag in H. exact H.
  - right. exists (sII_spoil W K). intros sI Hwin. unfold wins_I in Hwin.
    apply (notwinI_invariant W K sI Hn K (Nat.le_refl _)).
    rewrite Nat.sub_diag. exact Hwin.
Qed.

Print Assumptions zermelo_determinacy.
