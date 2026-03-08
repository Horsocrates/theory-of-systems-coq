(** * AuctionTheory.v -- Auction Mechanisms

    Theory of Systems -- Verified Standard Library (Batch 5)

    Elements: bids (list Q), valuations (list Q)
    Roles:    bidder_i -> Participant, auctioneer -> Mechanism
    Rules:    allocation rule + payment rule (constitution)
    Status:   truthful | manipulable | efficient | revenue_optimal

    Connection: GameTheory.v -- auctions as strategic games

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Core Types                                                        *)
(* ================================================================ *)

Definition Bid := Q.
Definition Bids := list Q.

(** Retrieve the i-th bid, defaulting to 0. *)
Definition nth_bid (bids : list Q) (i : nat) : Q := nth i bids 0.

(* ================================================================ *)
(* Winner Determination                                              *)
(* ================================================================ *)

(** Find the index of the highest bid.
    Traverses the list, tracking the best index and best value seen so far.
    Ties are broken in favor of the earlier (lower-index) bidder. *)
Fixpoint max_bid_idx (bids : list Q) (best_idx cur_idx : nat) (best_val : Q) : nat :=
  match bids with
  | [] => best_idx
  | b :: rest =>
    if Qlt_le_dec best_val b then
      max_bid_idx rest cur_idx (S cur_idx) b
    else
      max_bid_idx rest best_idx (S cur_idx) best_val
  end.

(** Winner of an auction: index of the highest bidder. *)
Definition winner (bids : list Q) : nat :=
  match bids with
  | [] => 0%nat
  | b :: rest => max_bid_idx rest 0%nat 1%nat b
  end.

(* ================================================================ *)
(* Payment Rules                                                     *)
(* ================================================================ *)

(** First-price auction: winner pays their own bid. *)
Definition first_price_payment (bids : list Q) : Q :=
  nth_bid bids (winner bids).

(** Find the maximum bid value excluding one bidder (by index). *)
Fixpoint max_excluding (bids : list Q) (exclude : nat) (cur_idx : nat) (best_val : Q) : Q :=
  match bids with
  | [] => best_val
  | b :: rest =>
    if Nat.eqb cur_idx exclude then
      max_excluding rest exclude (S cur_idx) best_val
    else
      if Qlt_le_dec best_val b then
        max_excluding rest exclude (S cur_idx) b
      else
        max_excluding rest exclude (S cur_idx) best_val
  end.

(** Second-price (Vickrey) auction: winner pays the second-highest bid.
    Implemented as the maximum bid excluding the winner. *)
Definition second_price_payment (bids : list Q) : Q :=
  max_excluding bids (winner bids) 0%nat 0.

(* ================================================================ *)
(* Vickrey Payoff                                                    *)
(* ================================================================ *)

(** Bidder i's payoff in a Vickrey (second-price) auction:
    - If i is the winner: value_i - second_highest_bid
    - Otherwise: 0 *)
Definition vickrey_payoff (bids : list Q) (values : list Q) (i : nat) : Q :=
  if Nat.eqb (winner bids) i then
    nth_bid values i - second_price_payment bids
  else
    0.

(* ================================================================ *)
(* Theorems: Winner Properties                                       *)
(* ================================================================ *)

(** Helper: max_bid_idx on an empty list returns best_idx. *)
Lemma max_bid_idx_nil : forall best_idx cur_idx best_val,
  max_bid_idx [] best_idx cur_idx best_val = best_idx.
Proof. reflexivity. Qed.

(** Winner of a singleton list is always bidder 0. *)
Theorem winner_singleton : forall b, winner [b] = 0%nat.
Proof.
  intros b. unfold winner. simpl. reflexivity.
Qed.

(** If the first bid is >= the second, bidder 0 wins. *)
Theorem winner_two_first : forall b1 b2,
  b1 >= b2 -> winner [b1; b2] = 0%nat.
Proof.
  intros b1 b2 Hge.
  unfold winner, max_bid_idx.
  destruct (Qlt_le_dec b1 b2) as [Hlt | Hle].
  - lra.
  - reflexivity.
Qed.

(** If the second bid is strictly greater, bidder 1 wins. *)
Theorem winner_two_second : forall b1 b2,
  b2 > b1 -> winner [b1; b2] = 1%nat.
Proof.
  intros b1 b2 Hgt.
  unfold winner, max_bid_idx.
  destruct (Qlt_le_dec b1 b2) as [Hlt | Hle].
  - reflexivity.
  - lra.
Qed.

(** Winner is deterministic: same input yields same output.
    This is trivially true by Coq's functional nature. *)
Theorem winner_deterministic : forall bids1 bids2 : list Q,
  bids1 = bids2 -> winner bids1 = winner bids2.
Proof.
  intros bids1 bids2 Heq. rewrite Heq. reflexivity.
Qed.

(* ================================================================ *)
(* Theorems: First-Price Payment                                     *)
(* ================================================================ *)

(** In a singleton auction, the payment equals the only bid. *)
Theorem first_price_singleton : forall b,
  first_price_payment [b] == b.
Proof.
  intros b. unfold first_price_payment.
  rewrite winner_singleton. unfold nth_bid. simpl. lra.
Qed.

(** If all bids are non-negative, the first-price payment is non-negative.
    Proved for the two-bidder case. *)
Theorem first_price_payment_nonneg_two : forall b1 b2,
  b1 >= 0 -> b2 >= 0 ->
  first_price_payment [b1; b2] >= 0.
Proof.
  intros b1 b2 H1 H2.
  unfold first_price_payment, winner, max_bid_idx.
  destruct (Qlt_le_dec b1 b2) as [Hlt | Hle].
  - unfold nth_bid. simpl. lra.
  - unfold nth_bid. simpl. lra.
Qed.

(* ================================================================ *)
(* Theorems: Second-Price Payment                                    *)
(* ================================================================ *)

(** Helper: max_excluding on empty list returns best_val. *)
Lemma max_excluding_nil : forall exclude cur_idx best_val,
  max_excluding [] exclude cur_idx best_val = best_val.
Proof. reflexivity. Qed.

(** In a two-bidder auction where b1 >= b2, the second-price payment is b2. *)
Theorem second_price_two_first_wins : forall b1 b2,
  b1 >= b2 -> b2 >= 0 ->
  second_price_payment [b1; b2] == b2.
Proof.
  intros b1 b2 Hge Hnn.
  unfold second_price_payment.
  rewrite winner_two_first by lra.
  unfold max_excluding. simpl.
  destruct (Qlt_le_dec 0 b2) as [Hlt | Hle].
  - reflexivity.
  - assert (b2 == 0) by lra. lra.
Qed.

(** In a two-bidder auction where b2 > b1, the second-price payment is b1. *)
Theorem second_price_two_second_wins : forall b1 b2,
  b2 > b1 -> b1 >= 0 ->
  second_price_payment [b1; b2] == b1.
Proof.
  intros b1 b2 Hgt Hnn.
  unfold second_price_payment.
  rewrite winner_two_second by lra.
  unfold max_excluding. simpl.
  destruct (Qlt_le_dec 0 b1) as [Hlt | Hle].
  - reflexivity.
  - assert (b1 == 0) by lra. lra.
Qed.

(* ================================================================ *)
(* Theorems: Vickrey Payoffs                                         *)
(* ================================================================ *)

(** The winner's payoff in a Vickrey auction is value - second_highest. *)
Theorem vickrey_winner_payoff : forall bids values,
  vickrey_payoff bids values (winner bids) ==
    nth_bid values (winner bids) - second_price_payment bids.
Proof.
  intros bids values.
  unfold vickrey_payoff. rewrite Nat.eqb_refl. lra.
Qed.

(** A non-winner's payoff in a Vickrey auction is 0. *)
Theorem vickrey_loser_payoff : forall bids values i,
  winner bids <> i ->
  vickrey_payoff bids values i == 0.
Proof.
  intros bids values i Hneq.
  unfold vickrey_payoff.
  destruct (Nat.eqb_spec (winner bids) i) as [Heq | _].
  - exfalso. exact (Hneq Heq).
  - lra.
Qed.

(* ================================================================ *)
(* Theorem: Vickrey Truthfulness (2-bidder case)                     *)
(* ================================================================ *)

(** In a 2-bidder Vickrey auction, bidding truthfully (bid = value)
    is weakly dominant for bidder 0.
    That is, for any alternative bid b', bidder 0's payoff when bidding v1
    is at least as good as when bidding b'. *)
Theorem vickrey_truthful_two_bidder0 : forall v1 b2 b',
  v1 >= 0 -> b2 >= 0 -> b' >= 0 ->
  vickrey_payoff [v1; b2] [v1; b2] 0%nat >=
  vickrey_payoff [b'; b2] [v1; b2] 0%nat.
Proof.
  intros v1 b2 b' Hv1 Hb2 Hb'.
  unfold vickrey_payoff, winner, max_bid_idx, second_price_payment, max_excluding, nth_bid.
  simpl.
  destruct (Qlt_le_dec v1 b2) as [Hlt1 | Hle1];
  destruct (Qlt_le_dec b' b2) as [Hlt2 | Hle2];
  simpl.
  - (* v1 < b2, b' < b2: both lose, payoff 0 = 0 *)
    lra.
  - (* v1 < b2, b' >= b2: truthful loses, deviant wins *)
    (* deviant payoff = v1 - b2 <= 0 since v1 < b2 *)
    destruct (Qlt_le_dec 0 b2) as [H3 | H3]; lra.
  - (* v1 >= b2, b' < b2: truthful wins, deviant loses *)
    (* truthful payoff = v1 - b2 >= 0 *)
    destruct (Qlt_le_dec 0 b2) as [H3 | H3].
    + lra.
    + assert (Hb2z : b2 == 0) by lra. lra.
  - (* v1 >= b2, b' >= b2: both win *)
    (* both get payoff v1 - b2 *)
    destruct (Qlt_le_dec 0 b2) as [H3 | H3];
    destruct (Qlt_le_dec 0 b2) as [H4 | H4]; lra.
Qed.

(** Symmetrically, truthful bidding is weakly dominant for bidder 1. *)
Theorem vickrey_truthful_two_bidder1 : forall b1 v2 b',
  b1 >= 0 -> v2 >= 0 -> b' >= 0 ->
  vickrey_payoff [b1; v2] [b1; v2] 1%nat >=
  vickrey_payoff [b1; b'] [b1; v2] 1%nat.
Proof.
  intros b1 v2 b' Hb1 Hv2 Hb'.
  unfold vickrey_payoff, winner, max_bid_idx, second_price_payment, max_excluding, nth_bid.
  simpl.
  destruct (Qlt_le_dec b1 v2) as [Hlt1 | Hle1];
  destruct (Qlt_le_dec b1 b') as [Hlt2 | Hle2];
  simpl.
  - (* b1 < v2, b1 < b': both win as bidder 1 *)
    (* payoff = v2 - b1 in both cases *)
    destruct (Qlt_le_dec 0 b1) as [H3 | H3];
    destruct (Qlt_le_dec 0 b1) as [H4 | H4]; lra.
  - (* b1 < v2, b1 >= b': truthful wins, deviant loses *)
    (* truthful payoff = v2 - b1 >= 0, deviant = 0 *)
    destruct (Qlt_le_dec 0 b1) as [H3 | H3].
    + lra.
    + assert (b1 == 0) by lra. lra.
  - (* b1 >= v2, b1 < b': truthful loses, deviant wins *)
    (* deviant payoff = v2 - b1 <= 0 *)
    destruct (Qlt_le_dec 0 b1) as [H3 | H3]; lra.
  - (* b1 >= v2, b1 >= b': both lose *)
    lra.
Qed.

(* ================================================================ *)
(* Theorems: max_excluding properties                                *)
(* ================================================================ *)

(** For two bidders where b1 >= b2 (bidder 0 wins),
    the second-highest bid <= the highest bid. *)
Theorem max_excluding_le_max_two : forall b1 b2,
  b1 >= b2 -> b2 >= 0 ->
  second_price_payment [b1; b2] <= first_price_payment [b1; b2].
Proof.
  intros b1 b2 Hge Hnn.
  unfold second_price_payment, first_price_payment.
  rewrite winner_two_first by lra.
  unfold max_excluding, nth_bid. simpl.
  destruct (Qlt_le_dec 0 b2) as [Hlt | Hle]; lra.
Qed.

(* ================================================================ *)
(* Revenue Comparison                                                *)
(* ================================================================ *)

(** In a two-bidder auction where b1 >= b2, first-price revenue >= second-price. *)
Theorem first_price_ge_second_price_two : forall b1 b2,
  b1 >= b2 -> b2 >= 0 ->
  first_price_payment [b1; b2] >= second_price_payment [b1; b2].
Proof.
  intros b1 b2 Hge Hnn.
  unfold first_price_payment, second_price_payment.
  rewrite winner_two_first by lra.
  unfold max_excluding, nth_bid. simpl.
  destruct (Qlt_le_dec 0 b2) as [Hlt | Hle]; lra.
Qed.

(* ================================================================ *)
(* Concrete Examples                                                 *)
(* ================================================================ *)

(** --- 2-bidder auction: bids = [10; 7] --- *)

Example ex_winner_2 : winner [10; 7] = 0%nat.
Proof. unfold winner, max_bid_idx. simpl. destruct (Qlt_le_dec 10 7); lra || reflexivity. Qed.

Example ex_first_price_2 : first_price_payment [10; 7] == 10.
Proof.
  unfold first_price_payment. rewrite ex_winner_2.
  unfold nth_bid. simpl. lra.
Qed.

Example ex_second_price_2 : second_price_payment [10; 7] == 7.
Proof.
  unfold second_price_payment. rewrite ex_winner_2.
  unfold max_excluding. simpl.
  destruct (Qlt_le_dec 0 7); lra || reflexivity.
Qed.

(** --- 3-bidder auction: bids = [5; 8; 3] --- *)

Example ex_winner_3 : winner [5; 8; 3] = 1%nat.
Proof.
  unfold winner, max_bid_idx. simpl.
  destruct (Qlt_le_dec 5 8) as [H1 | H1]; try lra.
  destruct (Qlt_le_dec 8 3) as [H2 | H2]; try lra.
  reflexivity.
Qed.

Example ex_first_price_3 : first_price_payment [5; 8; 3] == 8.
Proof.
  unfold first_price_payment. rewrite ex_winner_3.
  unfold nth_bid. simpl. lra.
Qed.

Example ex_second_price_3 : second_price_payment [5; 8; 3] == 5.
Proof.
  unfold second_price_payment. rewrite ex_winner_3.
  unfold max_excluding. simpl.
  destruct (Qlt_le_dec 0 5) as [H1 | H1];
  destruct (Qlt_le_dec 5 3) as [H2 | H2]; try lra; reflexivity.
Qed.

(** TOTAL: 22 Qed, 0 Admitted, 0 axioms *)
