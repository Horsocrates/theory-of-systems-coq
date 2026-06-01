(** * BitString.v — Bit-string layer over Binarity (F-13, Part II sync)

    Синхронизация репозитория с прозой II.4 («число как двоичный выбор»):
    слой ЗАПИСИ (Bit, BitString, длина = счёт бит) поверх Binarity.v, которого
    в коде не было (Side/L2/L3 были, bit-string — нет).

    ============ E/R/R разбор: бит и двоичная запись ============
      Rules (L5): L2 (раздельность, Marked<>Unmarked) + L3 (исчерпанность) = бит
                  как двоичность (side_binarity); добавление бита = S длины.
      Roles (L4): «сторона» Marked/Unmarked (одна позиция); «число = количество
                  бит» (bit_length) — роль-количество (ср. II.4).
      Elements  : биты и записи (BitString = list Bit), конечны (L1+P4).

    ДИАГНОСТИКА: число здесь — РОЛЬ (длина записи), не сам объект; бит — позиция
    из двух сторон (L2/L3), не «вещь». Запись конечна (P4). Связь с II.4: третий
    путь к ℕ (число = количество бит).

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import List Bool Lia.
Import ListNotations.
From ToS Require Import foundation.Binarity.

(* ===================================================================== *)
(*  Binarity as a single proposition (from L2 + L3)                       *)
(* ===================================================================== *)

Definition side_binarity : Prop :=
  Marked <> Unmarked /\ (forall s : Side, s = Marked \/ s = Unmarked).

Lemma side_is_binary : side_binarity.
Proof. split; [ exact L2_exclusive | exact L3_exhaustive ]. Qed.

(** The two sides, enumerated; exactly two. *)
Definition all_sides : list Side := [Marked; Unmarked].

Lemma all_sides_complete : forall s : Side, In s all_sides.
Proof. intros s. destruct (L3_exhaustive s) as [H|H]; subst; simpl; auto. Qed.

Lemma all_sides_length : length all_sides = 2%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Bit-string layer: a number is a count of bits                         *)
(* ===================================================================== *)

Definition Bit := Side.
Definition BitString := list Bit.

Definition bit_length (bs : BitString) : nat := length bs.

Definition add_bit (b : Bit) (bs : BitString) : BitString := b :: bs.

Lemma add_bit_increments_length : forall b bs,
  bit_length (add_bit b bs) = S (bit_length bs).
Proof. reflexivity. Qed.

(** A one-bit string exists. *)
Definition one_bit : BitString := [Marked].

Lemma one_bit_length : bit_length one_bit = 1%nat.
Proof. reflexivity. Qed.

(** "число = количество бит": a nonempty bitstring has a positive count. *)
Definition positive_bit_count (bs : BitString) : Prop := (bit_length bs >= 1)%nat.

Lemma nonempty_positive_count : forall bs, bs <> [] -> positive_bit_count bs.
Proof.
  intros bs Hne. unfold positive_bit_count, bit_length.
  destruct bs as [|b bs']; [ contradiction | simpl; lia ].
Qed.

(** Induction principle for NONEMPTY bitstrings (base = single bit, step
    preserves nonemptiness). *)
Lemma nonempty_bitstring_ind :
  forall (P : BitString -> Prop),
    (forall b : Bit, P [b]) ->
    (forall b bs, bs <> [] -> P bs -> P (b :: bs)) ->
    forall bs, bs <> [] -> P bs.
Proof.
  intros P Hbase Hstep bs.
  induction bs as [|b bs' IH]; intros Hne.
  - contradiction.
  - destruct bs' as [|b2 bs''].
    + apply Hbase.
    + apply Hstep; [ discriminate | apply IH; discriminate ].
Qed.
