(** * ProcessWalshCharacter.v — Walsh functions are characters of the Boolean group
      (ℤ₂ⁿ, ⊕) (Part VII, Batch 2 / proposal B1)

    Elements: rational ±1 values; indices i,a,b < 2ᵏ; bits (Nat.testbit)
    Roles:    had k i (·) = a character (homomorphism (ℤ₂ⁿ,⊕) → {±1}); ⊕ = group op
    Rules:    had k i (a ⊕ b) = had k i a · had k i b  (the character / homomorphism law)

    The Sylvester–Hadamard rows are not just ±1 vectors: each row had k i (·) is a
    CHARACTER of the Boolean group (ℤ₂ⁿ, XOR) — it turns the group operation ⊕ into the
    product ·. Proved by induction on k over ℚ, 0 axioms, from two bit facts about
    Nat.lxor and powers of two (low bits commute with mod; the leading bit of a XOR is
    the XOR of the leading bits). This is the algebraic heart of the Walsh convolution
    theorem (proposal B2): it lets H turn dyadic convolution into a pointwise product.

    HONEST FRONTIER: the GENERAL convolution theorem H(f∗g)=(Hf)·(Hg) for all 2ᵏ (B2)
    additionally needs reindexing a finite sum under the XOR-bijection n↦n⊕m — a q_sum
    permutation-invariance argument, the next brick.

    ============ E/R/R разбор ============
      Rules (L5): had k i (a⊕b)=had k i a·had k i b — характер; ⊕ ↦ · (гомоморфизм).
      Roles (L4): had k i · = роль-характер (ℤ₂ⁿ,⊕)→{±1}; ⊕ = групповая операция.
      Elements  : рациональные ±1, индексы i,a,b<2ᵏ, биты Nat.testbit (L1+P4).
    ДИАГНОСТИКА: характер — точное тождество над ℚ (0 акс); общая свёртка (B2) =
    характер + переиндексация q_sum под XOR-биекцией (фронтир).

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa Bool Arith NArith.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessWalshHadamard.   (* had, pow2, pow2_pos *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Bit-level facts about Nat.lxor and powers of two                       *)
(* ===================================================================== *)

(** The file's pow2 is 2^k. *)
Lemma pow2_eq : forall k, pow2 k = (2 ^ k)%nat.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - cbn [pow2 Nat.pow]. rewrite IH. reflexivity.
Qed.

(** A value below 2ⁿ has no bits at or above position n. *)
Lemma testbit_high_pow2 : forall a n m,
  (a < pow2 n)%nat -> (n <= m)%nat -> Nat.testbit a m = false.
Proof.
  intros a n m Ha Hnm. rewrite Nat.testbit_eqb. rewrite pow2_eq in Ha.
  assert (Ha2 : (a < 2 ^ m)%nat).
  { apply Nat.lt_le_trans with (2 ^ n)%nat.
    - exact Ha.
    - apply Nat.pow_le_mono_r; lia. }
  rewrite (Nat.div_small a (2 ^ m) Ha2). reflexivity.
Qed.

(** Conversely, no bits at or above n forces x < 2ⁿ. *)
Lemma lt_pow2_of_high_bits : forall x n,
  (forall m, (n <= m)%nat -> Nat.testbit x m = false) -> (x < 2 ^ n)%nat.
Proof.
  intros x n Hhigh.
  assert (Heq : x = (x mod 2 ^ n)%nat).
  { apply Nat.bits_inj. intros m.
    destruct (Nat.lt_ge_cases m n) as [Hlt | Hge].
    - rewrite (Nat.mod_pow2_bits_low x n m Hlt). reflexivity.
    - rewrite (Nat.mod_pow2_bits_high x n m Hge). exact (Hhigh m Hge). }
  rewrite Heq at 1. apply Nat.mod_upper_bound. apply Nat.pow_nonzero. lia.
Qed.

(** Low bits: XOR commutes with reduction mod 2ᵏ. *)
Lemma lxor_mod_pow2 : forall a b k,
  (Nat.lxor a b mod pow2 k)%nat = Nat.lxor (a mod pow2 k) (b mod pow2 k).
Proof.
  intros a b k. rewrite !pow2_eq.
  apply Nat.bits_inj. intros m.
  destruct (Nat.lt_ge_cases m k) as [Hlt | Hge].
  - rewrite (Nat.mod_pow2_bits_low (Nat.lxor a b) k m Hlt), !Nat.lxor_spec.
    rewrite (Nat.mod_pow2_bits_low a k m Hlt), (Nat.mod_pow2_bits_low b k m Hlt).
    reflexivity.
  - rewrite (Nat.mod_pow2_bits_high (Nat.lxor a b) k m Hge), Nat.lxor_spec.
    rewrite (Nat.mod_pow2_bits_high a k m Hge), (Nat.mod_pow2_bits_high b k m Hge).
    reflexivity.
Qed.

(** For x < 2^{k+1}, "x ≥ 2ᵏ" IS the k-th bit. *)
Lemma leb_pow2_testbit : forall k x, (x < pow2 (S k))%nat ->
  Nat.leb (pow2 k) x = Nat.testbit x k.
Proof.
  intros k x Hx.
  rewrite Nat.testbit_eqb, pow2_eq.
  assert (Hx2 : (x < 2 * 2 ^ k)%nat).
  { rewrite pow2_eq in Hx. simpl in Hx. lia. }
  assert (Hp : (2 ^ k <> 0)%nat) by (apply Nat.pow_nonzero; lia).
  assert (Hd : (x / 2 ^ k < 2)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  pose proof (Nat.div_mod_eq x (2 ^ k)) as Hdm.
  pose proof (Nat.mod_upper_bound x (2 ^ k) Hp) as Hr.
  assert (Hcase : (x / 2 ^ k = 0 \/ x / 2 ^ k = 1)%nat) by lia.
  destruct Hcase as [H0 | H1].
  - rewrite H0 in Hdm. rewrite Nat.mul_0_r in Hdm.
    rewrite H0. simpl. apply Nat.leb_gt. lia.
  - rewrite H1 in Hdm. rewrite Nat.mul_1_r in Hdm.
    rewrite H1. simpl. apply Nat.leb_le. lia.
Qed.

(** Leading bit: the leading bit of a XOR is the XOR of the leading bits. *)
Lemma leb_pow2_lxor : forall k a b,
  (a < pow2 (S k))%nat -> (b < pow2 (S k))%nat ->
  Nat.leb (pow2 k) (Nat.lxor a b) = xorb (Nat.leb (pow2 k) a) (Nat.leb (pow2 k) b).
Proof.
  intros k a b Ha Hb.
  assert (Hab : (Nat.lxor a b < pow2 (S k))%nat).
  { rewrite pow2_eq. apply lt_pow2_of_high_bits. intros m Hm.
    rewrite Nat.lxor_spec.
    rewrite (testbit_high_pow2 a (S k) m Ha Hm), (testbit_high_pow2 b (S k) m Hb Hm).
    reflexivity. }
  rewrite (leb_pow2_testbit k (Nat.lxor a b) Hab).
  rewrite (leb_pow2_testbit k a Ha), (leb_pow2_testbit k b Hb).
  apply Nat.lxor_spec.
Qed.

(* ===================================================================== *)
(*  THE CHARACTER PROPERTY: had k i (a ⊕ b) = had k i a · had k i b        *)
(* ===================================================================== *)

Theorem had_character : forall k i a b,
  (i < pow2 k)%nat -> (a < pow2 k)%nat -> (b < pow2 k)%nat ->
  had k i (Nat.lxor a b) == had k i a * had k i b.
Proof.
  induction k as [|k0 IH]; intros i a b Hi Ha Hb.
  - cbn [had]. ring.
  - pose proof (pow2_pos k0) as Hp0.
    assert (Hi' : (i mod pow2 k0 < pow2 k0)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Ha' : (a mod pow2 k0 < pow2 k0)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Hb' : (b mod pow2 k0 < pow2 k0)%nat) by (apply Nat.mod_upper_bound; lia).
    cbn [had].
    rewrite (lxor_mod_pow2 a b k0).
    rewrite (IH (i mod pow2 k0) (a mod pow2 k0) (b mod pow2 k0) Hi' Ha' Hb').
    rewrite (leb_pow2_lxor k0 a b Ha Hb).
    destruct (Nat.leb (pow2 k0) i), (Nat.leb (pow2 k0) a), (Nat.leb (pow2 k0) b);
      simpl; ring.
Qed.

(* Concrete witness: had 2 1 (1 ⊕ 2) = had 2 1 1 · had 2 1 2 (over ℚ). *)
Example had_character_ex :
  had 2 1 (Nat.lxor 1 2) == had 2 1 1 * had 2 1 2.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions had_character.
