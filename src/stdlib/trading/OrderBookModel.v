(* OrderBookModel.v — Order book structure with bid/ask analysis *)
(* E/R/R: Elements = Orders, Roles = Bid/Ask sides, Rules = Price priority *)
(* Trading Tier 4, File 1 *)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ===== Core Types ===== *)

Definition Order := (Q * Q)%type.  (* price, size *)
Definition OrderBook := (list Order * list Order)%type.  (* bids, asks *)

(* ===== Best Price Extraction ===== *)

Fixpoint best_price (orders : list Order) (cmp : Q -> Q -> bool) (acc : Q) : Q :=
  match orders with
  | nil => acc
  | (p, _) :: rest => if cmp p acc then best_price rest cmp p
                       else best_price rest cmp acc
  end.

Definition best_bid (book : OrderBook) : Q :=
  match fst book with
  | nil => 0
  | (p, _) :: rest => best_price rest (fun a b => Qle_bool b a) p
  end.

Definition best_ask (book : OrderBook) : Q :=
  match snd book with
  | nil => 0
  | (p, _) :: rest => best_price rest (fun a b => Qle_bool a b) p
  end.

(* ===== Mid Price and Spread ===== *)

Definition mid_price (book : OrderBook) : Q :=
  (best_bid book + best_ask book) / (2#1).

Definition spread (book : OrderBook) : Q :=
  best_ask book - best_bid book.

(* ===== Volume ===== *)

Fixpoint total_volume_side (orders : list Order) : Q :=
  match orders with
  | nil => 0
  | (_, s) :: rest => s + total_volume_side rest
  end.

Definition bid_volume (book : OrderBook) : Q :=
  total_volume_side (fst book).

Definition ask_volume (book : OrderBook) : Q :=
  total_volume_side (snd book).

Definition total_volume (book : OrderBook) : Q :=
  bid_volume book + ask_volume book.

(* ===== Imbalance ===== *)

Definition imbalance (book : OrderBook) : Q :=
  let bv := bid_volume book in
  let av := ask_volume book in
  (bv - av) / (bv + av).

(* ===== Wall Detection ===== *)

Definition has_wall (orders : list Order) : bool :=
  List.existsb (fun o => Qle_bool 50 (snd o)) orders.

(* ===== Depth Within Range ===== *)

Fixpoint depth_within (orders : list Order) (lo hi : Q) : Q :=
  match orders with
  | nil => 0
  | (p, s) :: rest =>
      if andb (Qle_bool lo p) (Qle_bool p hi)
      then s + depth_within rest lo hi
      else depth_within rest lo hi
  end.

(* ===== Book Signal ===== *)

Definition book_signal (book : OrderBook) : Z :=
  let imb := imbalance book in
  match Qlt_le_dec (1#5) imb with
  | left _ => 1%Z    (* bid heavy => bullish *)
  | right _ =>
    match Qlt_le_dec imb (-(1#5)) with
    | left _ => (-1)%Z  (* ask heavy => bearish *)
    | right _ => 0%Z    (* balanced *)
    end
  end.

(* ===== Concrete Example ===== *)

Definition example_bids : list Order :=
  [(100, 5); (99, 10); (98, 20)].

Definition example_asks : list Order :=
  [(101, 3); (102, 8); (103, 15)].

Definition example_book : OrderBook :=
  (example_bids, example_asks).

(* ===== Lemmas ===== *)

Lemma best_bid_example : best_bid example_book = 100.
Proof. vm_compute. reflexivity. Qed.

Lemma best_ask_example : best_ask example_book = 101.
Proof. vm_compute. reflexivity. Qed.

Lemma mid_price_example : mid_price example_book = 201 # 2.
Proof. vm_compute. reflexivity. Qed.

Lemma spread_example : spread example_book = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma bid_volume_example : bid_volume example_book = 35.
Proof. vm_compute. reflexivity. Qed.

Lemma ask_volume_example : ask_volume example_book = 26.
Proof. vm_compute. reflexivity. Qed.

Lemma total_volume_example : total_volume example_book = 61.
Proof. vm_compute. reflexivity. Qed.

Lemma imbalance_example : imbalance example_book = 9 # 61.
Proof. vm_compute. reflexivity. Qed.

(* Wall detection *)
Lemma no_bid_wall : has_wall example_bids = false.
Proof. vm_compute. reflexivity. Qed.

Lemma no_ask_wall : has_wall example_asks = false.
Proof. vm_compute. reflexivity. Qed.

Definition wall_asks : list Order := [(101, 3); (102, 60); (103, 15)].

Lemma has_ask_wall : has_wall wall_asks = true.
Proof. vm_compute. reflexivity. Qed.

(* Depth within range *)
Lemma depth_bids_98_100 : depth_within example_bids 98 100 = 35.
Proof. vm_compute. reflexivity. Qed.

Lemma depth_bids_99_100 : depth_within example_bids 99 100 = 15.
Proof. vm_compute. reflexivity. Qed.

Lemma depth_asks_101_102 : depth_within example_asks 101 102 = 11.
Proof. vm_compute. reflexivity. Qed.

(* Book signal: 9/61 ~ 0.148 < 1/5 = 0.2 and > -1/5, so balanced *)
Lemma book_signal_example : book_signal example_book = 0%Z.
Proof.
  unfold book_signal, imbalance, bid_volume, ask_volume, total_volume_side,
         example_book, example_bids, example_asks, fst, snd.
  destruct (Qlt_le_dec (1#5) ((35 - 26) / (35 + 26))).
  - exfalso. unfold Qlt in q. simpl in q. lia.
  - destruct (Qlt_le_dec ((35 - 26) / (35 + 26)) (-(1#5))).
    + exfalso. unfold Qlt in q0. simpl in q0. lia.
    + reflexivity.
Qed.

(* Strongly bid-heavy book *)
Definition heavy_bid_book : OrderBook :=
  ([(100, 80); (99, 50)], [(101, 3)]).

Lemma heavy_bid_imbalance : imbalance heavy_bid_book = 127 # 133.
Proof. vm_compute. reflexivity. Qed.

Lemma heavy_bid_signal : book_signal heavy_bid_book = 1%Z.
Proof.
  unfold book_signal, imbalance, bid_volume, ask_volume, total_volume_side,
         heavy_bid_book, fst, snd.
  destruct (Qlt_le_dec (1#5) ((130 - 3) / (130 + 3))).
  - reflexivity.
  - exfalso. unfold Qle in q. simpl in q. lia.
Qed.

(* Strongly ask-heavy book *)
Definition heavy_ask_book : OrderBook :=
  ([(100, 2)], [(101, 50); (102, 40)]).

Lemma heavy_ask_imbalance : imbalance heavy_ask_book = -(88 # 92).
Proof. vm_compute. reflexivity. Qed.

Lemma heavy_ask_signal : book_signal heavy_ask_book = (-1)%Z.
Proof.
  unfold book_signal, imbalance, bid_volume, ask_volume, total_volume_side,
         heavy_ask_book, fst, snd.
  destruct (Qlt_le_dec (1#5) ((2 - 90) / (2 + 90))).
  - exfalso. unfold Qlt in q. simpl in q. lia.
  - destruct (Qlt_le_dec ((2 - 90) / (2 + 90)) (-(1#5))).
    + reflexivity.
    + exfalso. unfold Qle in q0. simpl in q0. lia.
Qed.

(* ===== Structural Properties ===== *)

Lemma spread_eq : forall book, spread book == best_ask book - best_bid book.
Proof. intros. unfold spread. ring. Qed.

Lemma volume_sum : forall book,
  total_volume book == bid_volume book + ask_volume book.
Proof. intros. unfold total_volume. ring. Qed.

Lemma empty_book_volume : total_volume (nil, nil) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma empty_book_bid : best_bid (nil, nil) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma empty_book_ask : best_ask (nil, nil) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma imbalance_symmetric_book :
  imbalance ([(100, 10)], [(101, 10)]) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma depth_empty : depth_within nil 0 100 = 0.
Proof. vm_compute. reflexivity. Qed.
