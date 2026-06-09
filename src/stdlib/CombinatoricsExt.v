(** * CombinatoricsExt.v — Каталан и общая симметрия выбора (расширение Combinatorics.v)
      Закрывает gap дискретной части (Часть XVI): Combinatorics.v даёт факториал, биномиальные
      коэффициенты (рекуррентность Паскаля) и принцип Дирихле, но ОБЩУЮ симметрию выбора
      binom(n,k)=binom(n,n−k) (лишь конкретные примеры) и числа Каталана НЕ содержит.  Всё здесь —
      конечный счёт над nat, 0 аксиом.

    Elements: натуральные n,k; биномиальные коэффициенты; числа Каталана
    Roles:    n = размер вселенной, k = размер выборки; катаplanовское C_n = роль-счёт
              (число корректных скобочных структур / путей Дика)
    Rules:    рекуррентность Паскаля (из Combinatorics.v); двойственность выбора (симметрия);
              замкнутая форма Каталана C_n = binom(2n,n) − binom(2n,n+1)

    ============ E/R/R разбор ============
      Rules (L5): рекуррентность Паскаля + замкнутая форма Каталана — правила СЧЁТА конечных
                  структур; симметрия binom(n,k)=binom(n,n−k) — правило двойственности выбора.
      Roles (L4): k = роль-размер выборки; C_n = роль-счёт класса структур.
      Elements  : конкретные n,k и значения binom/catalan — конечно-актуальные (P4).
    ДИАГНОСТИКА (P4): всё здесь — конечный счёт (Element-сторона границы финитизации): значения
      вычисляются за конечное число шагов. Бесконечная комбинаторика (бесконечный Рамсей, общие
      производящие функции как завершённые объекты) — role-limit, не здесь.

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Lia List.
From ToS Require Import stdlib.Combinatorics.
Import ListNotations.

(* ===================================================================== *)
(*  ОБЩАЯ СИММЕТРИЯ: binom(n,k) = binom(n, n−k) (двойственность выбора)    *)
(* ===================================================================== *)

(** Combinatorics.v доказывает лишь конкретные случаи (binomial_sym_4_1 и т.п.);
    здесь — общее тождество: выбрать k из n = оставить n−k. *)
Theorem binomial_sym : forall n k, k <= n -> binomial n k = binomial n (n - k).
Proof.
  induction n as [| n IH]; intros k Hk.
  - assert (k = 0) by lia. subst k. reflexivity.
  - destruct k as [| k].
    + rewrite Nat.sub_0_r, binomial_0_r, binomial_n_n. reflexivity.
    + assert (Hk' : k <= n) by lia.
      replace (S n - S k) with (n - k) by lia.
      destruct (Nat.eq_dec k n) as [Heq | Hne].
      * subst k. rewrite Nat.sub_diag, binomial_0_r, binomial_n_n. reflexivity.
      * assert (HSk : S k <= n) by lia.
        rewrite (pascal_identity n k).
        replace (n - k) with (S (n - S k)) by lia.
        rewrite (pascal_identity n (n - S k)).
        rewrite (IH (S k) HSk).
        rewrite (IH k Hk').
        replace (n - k) with (S (n - S k)) by lia.
        lia.
Qed.

(* ===================================================================== *)
(*  СУММА СТРОКИ ПАСКАЛЯ: Σ_{k=0}^{n} binom(n,k) = 2^n (число подмножеств) *)
(* ===================================================================== *)

(** Частичная сумма строки Σ_{k=0}^{m} binom(n,k). *)
Fixpoint rowsum (n m : nat) : nat :=
  match m with
  | O    => binomial n 0
  | S m' => rowsum n m' + binomial n (S m')
  end.

(** Рекуррентность строки по Паскалю (без вычитания над nat). *)
Lemma rowsum_pascal : forall n m, rowsum (S n) (S m) = rowsum n (S m) + rowsum n m.
Proof.
  intros n m. revert n. induction m as [| m IH]; intro n.
  - cbn [rowsum]. rewrite !binomial_0_r, !binomial_1_r. lia.
  - assert (E1 : rowsum (S n) (S (S m)) = rowsum (S n) (S m) + binomial (S n) (S (S m))) by reflexivity.
    assert (E2 : rowsum n (S (S m)) = rowsum n (S m) + binomial n (S (S m))) by reflexivity.
    assert (E3 : rowsum n (S m) = rowsum n m + binomial n (S m)) by reflexivity.
    rewrite E1. rewrite E2. rewrite IH. rewrite (pascal_identity n (S m)). rewrite E3. lia.
Qed.

Definition row_sum (n : nat) : nat := rowsum n n.

(** ★ Сумма строки Паскаля = число всех подмножеств n-множества. *)
Theorem row_sum_pow2 : forall n, row_sum n = 2 ^ n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - unfold row_sum in *.
    rewrite rowsum_pascal.
    assert (E : rowsum n (S n) = rowsum n n + binomial n (S n)) by reflexivity.
    rewrite E.
    rewrite (binomial_gt n (S n)) by lia.
    rewrite IH.
    change (2 ^ S n) with (2 * 2 ^ n).
    lia.
Qed.

(* ===================================================================== *)
(*  ЧИСЛА КАТАЛАНА: замкнутая форма C_n = binom(2n,n) − binom(2n,n+1)      *)
(* ===================================================================== *)

Definition catalan (n : nat) : nat := binomial (2 * n) n - binomial (2 * n) (n + 1).

Lemma catalan_0 : catalan 0 = 1.   Proof. vm_compute. reflexivity. Qed.
Lemma catalan_1 : catalan 1 = 1.   Proof. vm_compute. reflexivity. Qed.
Lemma catalan_2 : catalan 2 = 2.   Proof. vm_compute. reflexivity. Qed.
Lemma catalan_3 : catalan 3 = 5.   Proof. vm_compute. reflexivity. Qed.
Lemma catalan_4 : catalan 4 = 14.  Proof. vm_compute. reflexivity. Qed.
Lemma catalan_5 : catalan 5 = 42.  Proof. vm_compute. reflexivity. Qed.
Lemma catalan_6 : catalan 6 = 132. Proof. vm_compute. reflexivity. Qed.

(** Каталановское число не превосходит центрального биномиального — Element-граница счёта. *)
Corollary catalan_le_central : forall n, catalan n <= binomial (2 * n) n.
Proof. intro n. unfold catalan. lia. Qed.

(* ===================================================================== *)
(*  ПРИНЦИП ДИРИХЛЕ как Element-движок (мост к 15.2 / Рамсею)             *)
(* ===================================================================== *)

(** Пере-формулируем конечный принцип Дирихле (pigeonhole_simple из Combinatorics.v) как
    именованный «конечный движок» части: список из >n элементов в {0..n−1} имеет повтор.
    Та же голубятня, что закрывает накачку (15.2) и CRT (XIII) — Element-сторона. *)
Theorem finite_pigeonhole_engine :
  forall (l : list nat) (n : nat),
    length l > n -> (forall x, In x l -> x < n) -> NoDup l -> False.
Proof. exact pigeonhole_simple. Qed.

Print Assumptions binomial_sym.
Print Assumptions row_sum_pow2.
Print Assumptions catalan_le_central.
Print Assumptions finite_pigeonhole_engine.

(* ===================================================================== *)
(*  Сводка: общая симметрия binom(n,k)=binom(n,n−k); числа Каталана       *)
(*  (замкнутая форма + значения 0..6 + центральная граница); голубятня    *)
(*  как Element-движок. Всё 0-аксиомно, конечный счёт (P4). 10 Qed.       *)
(* ===================================================================== *)
