(** * DyadicBits.v — information in bits is Element-side only for DYADIC events: a
      trit (3 equally likely outcomes) carries log₂3 bits, which is IRRATIONAL (a
      role-limit), because 2^a = 3^b has no solution (parity).  You cannot measure
      base-3 information in an integer number of bits — the irrationality IS the
      fundamental encoding overhead.

    Elements: the integer bit-counts (k bits ↔ 2ᵏ outcomes); the powers 2^a, n^b;
              dyadic probabilities (L1 + P4)
    Roles:    log₂n for n a power of 2 = the Element side (an integer number of bits,
              exact codes); log₂3 (a trit's information) = a role-limit (an irrational
              number of bits); dyadic distributions = Element vs non-dyadic = role-limit
    Rules:    2^a vs n^b; parity (2^a is even for a≥1, odd^b is odd); log₂n is rational
              ⟺ 2^a = n^b is solvable; entropy / Kraft

    THE DEEP POINT — information measured in bits lands in ℚ only for dyadic events.
    A distribution whose probabilities are powers of 1/2 has an integer number of bits
    of information per symbol — exact prefix codes, the Element side.  But a uniform
    TRIT (three equally likely outcomes) carries log₂3 ≈ 1.585 bits, and this is
    IRRATIONAL: if log₂3 = a/b were rational then 2^a = 3^b, impossible — 2^a is even
    (for a≥1) while 3^b is odd (`log2_odd_irrational`, the same parity argument for any
    odd n>1: `log2_3_irrational`, `log2_5_irrational`).  So you cannot pack base-3
    information into a whole number of bits; the irrationality of log₂3 is exactly the
    unavoidable overhead of encoding a trit in bits.  The Element/role-limit boundary
    in information theory is dyadic vs non-dyadic: powers of two give exact integer-bit
    codes (finite, actual), everything else gives a role-limit number of bits.

    ============ E/R/R разбор ============
      Rules (L5): 2^a vs n^b; чётность (2^a чётно при a≥1, нечёт^b нечётно); log₂n
                  рационален ⟺ 2^a=n^b разрешимо; энтропия/Крафт.
      Roles (L4): log₂(2ᵏ) = Element (целое число бит); log₂3 (трит) = role-limit
                  (иррациональное число бит); диадическое vs не-диадическое.
      Elements  : целые счётчики бит (k ↔ 2ᵏ исходов); степени; диад. вероятности (L1+P4).
    ДИАГНОСТИКА (P4): информация в битах рациональна ТОЛЬКО для диадических событий; трит =
    log₂3 бит = role-limit (иррационально, 2^a≠3^b чётность). Иррациональность = фундаментальный
    оверхед кодирования. Граница = диадическое vs не-диадическое.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ================================================================= *)
(** ** Parity: odd^b is odd, 2^(a+1) is even                         *)
(* ================================================================= *)

Lemma odd_pow : forall n b : nat, Nat.odd n = true -> Nat.odd (n ^ b) = true.
Proof.
  intros n b H. induction b as [| b IH].
  - reflexivity.
  - simpl. rewrite Nat.odd_mul, H, IH. reflexivity.
Qed.

(* ================================================================= *)
(** ** log₂ n is irrational for odd n>1: 2^a = n^b has no solution    *)
(* ================================================================= *)

(** ★ For odd n>1, the equation 2^a = n^b has no solution with b≥1 — i.e. log₂n is
    irrational.  (2^a is even for a≥1 while n^b is odd; and 2^0=1 < n^b.)  So the
    information of a uniform n-symbol event is an irrational number of bits. *)
Theorem log2_odd_irrational : forall n : nat,
  Nat.odd n = true -> 2 <= n ->
  ~ (exists a b : nat, 1 <= b /\ 2 ^ a = n ^ b).
Proof.
  intros n Hodd Hn [a [b [Hb Heq]]].
  assert (Hnb : Nat.odd (n ^ b) = true) by (apply odd_pow; exact Hodd).
  destruct a as [| a'].
  - (* 2^0 = 1 = n^b, but n^b ≥ n ≥ 2 *)
    simpl in Heq.
    assert (H1 : n ^ 1 <= n ^ b) by (apply Nat.pow_le_mono_r; lia).
    rewrite Nat.pow_1_r in H1. lia.
  - (* 2^(S a') is even, n^b is odd *)
    assert (Heven : Nat.odd (2 ^ S a') = false).
    { change (2 ^ S a') with (2 * 2 ^ a'). rewrite Nat.odd_mul. reflexivity. }
    rewrite Heq, Hnb in Heven. discriminate.
Qed.

(** log₂3 is irrational: a uniform trit carries an irrational number of bits. *)
Corollary log2_3_irrational : ~ (exists a b : nat, 1 <= b /\ 2 ^ a = 3 ^ b).
Proof. apply log2_odd_irrational; [ reflexivity | lia ]. Qed.

(** log₂5 is irrational. *)
Corollary log2_5_irrational : ~ (exists a b : nat, 1 <= b /\ 2 ^ a = 5 ^ b).
Proof. apply log2_odd_irrational; [ reflexivity | lia ]. Qed.

(* ================================================================= *)
(** ** The Element side: dyadic — k bits encode 2ᵏ outcomes exactly   *)
(* ================================================================= *)

(** A dyadic event is exact: k bits address exactly 2ᵏ outcomes (here k=3 ↔ 8) — an
    integer number of bits, the Element side. *)
Theorem dyadic_exact : 2 ^ 3 = 8.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Synthesis                                                      *)
(* ================================================================= *)

(** Information in bits, split by the finitization boundary:
      (a) dyadic events are exact — k bits address 2ᵏ outcomes (Element side);
      (b) a uniform trit carries log₂3 bits, which is IRRATIONAL (2^a=3^b has no
          solution) — a role-limit number of bits;
      (c) likewise for any odd base n>1. *)
Theorem dyadic_bits_synthesis :
  (2 ^ 3 = 8)
  /\ ~ (exists a b : nat, 1 <= b /\ 2 ^ a = 3 ^ b)
  /\ (forall n : nat, Nat.odd n = true -> 2 <= n ->
        ~ (exists a b : nat, 1 <= b /\ 2 ^ a = n ^ b)).
Proof.
  split; [ exact dyadic_exact | ].
  split; [ exact log2_3_irrational | exact log2_odd_irrational ].
Qed.
